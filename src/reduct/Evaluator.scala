package reduct

import model.Expr
import model.Z
import model.S
import model.Var
import model.App
import model.Lam
import model.Fix
import model.Prog
import model.Triv
import model.PairEx
import model.InL
import model.InR
import model.UnitTy
import model.Match
import model.Rule
import model.Pattern
import model.ZPat
import model.SPat
import model.WildPat
import model.VarPat
import model.TrivPat
import model.InLPat
import model.InRPat
import model.PairPat
import model.Defn
import model.Value
import model.LamVal
import model.ZVal
import model.TrivVal
import model.SVal
import model.InLVal
import model.InRVal
import model.PairVal
import model.RecursiveLamVal
import model.GenericMap
import model.TyVar
import model.Nat
import model.Arrow
import model.Product
import model.Sum

object Evaluator {

  type State = (Target, List[Map[String, Value]], List[Stack])

  sealed abstract class Target
  case class Eval(e : Expr) extends Target
  case class Return(v : Value) extends Target

  def getBinding(e : List[Map[String, Value]], x : String) : Value = e match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m(x)
    case m :: e                  => getBinding(e, x)
  }

  def flattenEnv(e : List[Map[String, Value]]) : Map[String, Value] = e.foldRight(Map[String, Value]())({ case (m1, m2) => m2 ++ m1 })

  //All these are init'd to null, because they are manually set in each pass
  var target : Target = null //TODO use for all parts The expressionbeing evaluated or the vaue being returned
  var stack : List[Stack] = null //TODO use for all parts The parts of the expression whose evaluation has been deferred
  var env : List[Map[String, Value]] = null //TODO use for all parts The stack of variable-binding frames

  var rules : List[Rule] = null //Rules as yet untried
  var matchVal : Value = null //Value being matched against
  var body : Expr = null //The body to be evaluated if the match succeeds
  var patternStack : List[PatStack] = null //The parts of the pattern still unmatched
  var matchingTarget : MatchingTarget = null //Either a pattern against a variable, or a binding being returned

  def runEval(t : Target, m : List[Map[String, Value]]) : Value = eval(t, m, Nil)

  def eval : State => Value = {
    case (Eval(e), m, s) => e match {
      case Var(x)                                  => eval(Return(getBinding(m, x)), m, s)
      case Z                                       => eval(Return(ZVal), m, s)
      case S(n)                                    => eval(Eval(n), m, StackS :: s)
      case Lam(v, t, e)                            => eval(Return(LamVal(v, e, flattenEnv(m))), m, s)
      case App(e1, e2)                             => eval(Eval(e1), m, StackLam(e2) :: s)
      case Fix(v, t, Lam(x, t2, e))                => eval(Eval(Lam(x, t2, e)), Map(v -> RecursiveLamVal(v, x, e, flattenEnv(m))) :: m, PopFrame :: s)
      case Fix(v, t, e)                            => eval(Eval(e), m, s) //this will explode on CAFs (eg, recursive non-functions) so don't write them
      case Triv                                    => eval(Return(TrivVal), m, s)
      case PairEx(e1, e2)                          => eval(Eval(e1), m, StackLPair(e2) :: s)
      case InL(e, t)                               => eval(Eval(e), m, StackInL :: s)
      case InR(e, t)                               => eval(Eval(e), m, StackInR :: s)
      case Match(e, rs)                            => eval(Eval(e), m, StackCase(rs) :: s)
      case GenericMap(mu, TyVar(t), x, t2, e1, e2) => eval(Eval(e2), m, StackMap(x, e1) :: s)
      case GenericMap(mu, Nat, x, t2, e1, e2)      => eval(Eval(e2), m, s)
      case GenericMap(mu, UnitTy, x, t2, e1, e2)   => eval(Eval(e2), m, s)
      case GenericMap(mu, Product(st1, st2), x, t2, e1, PairEx(e2a, e2b)) =>
        eval(Eval(PairEx(GenericMap(mu, st1, x, t2, e1, e2a), GenericMap(mu, st2, x, t2, e1, e2b))), m, s)
      case GenericMap(mu, Sum(st1, st2), x, t2, e1, InL(e, t)) => eval(Eval(GenericMap(mu, st1, x, t2, e1, e)), m, s)
      case GenericMap(mu, Sum(st1, st2), x, t2, e1, InR(e, t)) => eval(Eval(GenericMap(mu, st2, x, t2, e1, e)), m, s)
      case GenericMap(mu, t1, x, t2, e1, e2)                   => throw new Exception("Type " + t1 + " does not match expression " + e2)
      //Typechecker should have caught this last, unless it was a function, which we refuse to allow (only polynomial generic types ATM)
    }
    case (Return(v), m, Nil) => v
    case (Return(v), m, stk :: s) => stk match {
      case StackS                       => eval(Return(SVal(v)), m, s)
      case StackLam(e2)                 => eval(Eval(e2), m, StackArg(v) :: s)
      case StackArg(LamVal(x, e, clos)) => eval(Eval(e), clos + (x -> v) :: m, PopFrame :: s)
      case StackArg(v1)                 => throw new Exception("Application of a non-function : " + v1) //Typechecker should have caught this
      case StackLPair(e2)               => eval(Eval(e2), m, StackRPair(v) :: s)
      case StackRPair(v1)               => eval(Return(PairVal(v1, v)), m, s)
      case StackInL                     => eval(Return(InLVal(v)), m, s)
      case StackInR                     => eval(Return(InRVal(v)), m, s)
      case StackCase(Nil)               => throw new Exception("Empty set of rules?")
      case StackCase(Rule(p, b) :: rs) => {
        rules = rs
        matchVal = v
        stack = s
        env = m
        body = b
        patternStack = Nil
        matchingTarget = Against(p, matchVal)

        while (!(matchingTarget.isInstanceOf[Binding] && patternStack.isEmpty)) {
          matchPattern
        }
        eval(Eval(body), matchingTarget.asInstanceOf[Binding].b :: env, PopFrame :: stack)
      }
      case StackMap(x, e1) => eval(Eval(e1), Map(x -> v) :: m, s)
      case PopFrame        => eval(Return(v), m.tail, s) //'tail' should be safe, pops are added only with a frame
    }
  }

  sealed abstract class MatchingTarget
  case class Against(p : Pattern, v : Value) extends MatchingTarget
  case class Binding(b : Map[String, Value]) extends MatchingTarget

  def matchPattern : Unit = matchingTarget match {
    case Against(WildPat, _)           => matchingTarget = Binding(Map())
    case Against(VarPat(x), v)         => matchingTarget = Binding(Map(x -> v))
    case Against(ZPat, ZVal)           => matchingTarget = Binding(Map())
    case Against(SPat(p), SVal(v))     => matchingTarget = Against(p, v)
    case Against(TrivPat, TrivVal)     => matchingTarget = Binding(Map())
    case Against(InLPat(p), InLVal(v)) => matchingTarget = Against(p, v)
    case Against(InRPat(p), InRVal(v)) => matchingTarget = Against(p, v)
    case Against(PairPat(p1, p2), PairVal(v1, v2)) => {
      patternStack = PatStackLPair(v2, p2) :: patternStack
      matchingTarget = Against(p1, v1)
    }
    case Against(_, _) => rules match { //Match failed; move on to the next pattern
      case Nil => throw new Exception("No pattern match found for " + matchVal)
      case Rule(p, b) :: rs => {
        rules = rs
        body = b
        patternStack = Nil
        matchingTarget = Against(p, matchVal)
      }
    }
    case Binding(bind) => patternStack match {
      case Nil => throw new Exception("Should have aborted the pattern-match driver loop!") //This is the escape case
      case PatStackLPair(v2, p2) :: ps => {
        patternStack = PatStackRPair(bind) :: ps
        matchingTarget = Against(p2, v2)
      }
      case PatStackRPair(m1) :: ps if ((m1.keySet & bind.keySet).isEmpty) => {
        patternStack = ps
        matchingTarget = Binding(m1 ++ bind)
      }
      case PatStackRPair(m1) :: ps => throw new Exception("Patterns cannot have repeated variables") //genuine error; as of now, no way to check
    }
  }

  def evalDefn(d : Defn, m : Map[String, Value]) : Map[String, Value] = m + (d.name -> runEval(Eval(d.body), List(m)))

  def evaluate(p : Prog) : Value = runEval(Eval(p.e), List(p.defs.foldRight(Map[String, Value]())(evalDefn)))

}