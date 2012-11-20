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
import model.ExprDefn
import model.Value
import model.LamVal
import model.ZVal
import model.TrivVal
import model.SVal
import model.InLVal
import model.InRVal
import model.PairVal
import model.RecursiveLamVal
import model.Fold
import model.Unfold
import model.FoldVal
import model.TypeLam
import model.TypeApp
import model.TypeLam
import model.TypeDefn

object Evaluator {

  sealed abstract class Target
  case class Eval(e : Expr) extends Target
  case class Return(v : Value) extends Target

  //All these are init'd to null, because they are manually set in each pass
  //Conceptually, this is a tail-recursive state-machine; for efficiency reasons we actually modify vars, but it's not strictly necessary
  var target : Target = null //The expression being evaluated or the value being returned
  var stack : List[Stack] = null //TODO use for all parts The parts of the expression whose evaluation has been deferred
  var env : List[Map[String, Value]] = null //The stack of variable-binding frames

  def push(s : Stack) : Unit = stack = s :: stack
  
  def pop : Stack = stack match {
    case Nil => throw new Exception("Should have aborted the eval driver loop!") //This is the escape case
    case s :: stk => {
      stack = stk
      s
    }
  }
  
  def getBinding(x : String) : Value = innerGetBinding(env, x)
  def innerGetBinding(e : List[Map[String, Value]], x : String) : Value = e match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m(x)
    case m :: e                  => innerGetBinding(e, x)
  }

  //Crush the env down into a single stack frame for use as a closure
  def flattenEnv : Map[String, Value] = env.foldRight(Map[String, Value]())({ case (m1, m2) => m2 ++ m1 })

  def runEval(t : Target, m : List[Map[String, Value]]) : Value = {
    target = t
    env = m
    stack = Nil

    while (!(target.isInstanceOf[Return] && stack.isEmpty)) {
      eval
    }
    target.asInstanceOf[Return].v
  }

  def eval : Unit = target match {
    case Eval(e) => e match {
      case Var(x) => target = Return(getBinding(x))
      case Z      => target = Return(ZVal)
      case S(n) => {
        target = Eval(n)
        push(StackS)
      }
      case Lam(v, t, e) => target = Return(LamVal(v, e, flattenEnv))
      case App(e1, e2) => {
        target = Eval(e1)
        push(StackLam(e2))
      }
      case Fix(v, Lam(x, t2, e)) => {
        env = Map(v -> RecursiveLamVal(v, x, e, flattenEnv)) :: env
        target = Eval(Lam(x, t2, e))
        push(PopFrame)
      }
      case Fix(v, e) => target = Eval(e) //this will explode on CAFs (eg, recursive non-functions) so don't write them
      case Triv         => target = Return(TrivVal)
      case PairEx(e1, e2) => {
        target = Eval(e1)
        push(StackLPair(e2))
      }
      case InL(e) => {
        target = Eval(e)
        push(StackInL)
      }
      case InR(e) => {
        target = Eval(e)
        push(StackInR)
      }
      case Match(e, rs) => {
        target = Eval(e)
        push(StackCase(rs))
      }
      case Fold(mu, t, e) => {
        target = Eval(e)
        push(StackFold)
      }
      case Unfold(e) => {
        target = Eval(e)
        push(StackUnfold)
      }
      case TypeLam(t, e) => target = Eval(e) //Ignore types
      case TypeApp(e, t) => target = Eval(e) //Ignore types
    }
    case Return(v) => pop match {
      case StackS => target = Return(SVal(v))
      case StackLam(e2) => {
        target = Eval(e2)
        push(StackArg(v))
      }
      case StackArg(LamVal(x, e, clos)) => {
        env = clos + (x -> v) :: env
        target = Eval(e)
        push(PopFrame)
      }
      case StackArg(v1) => throw new Exception("Application of a non-function : " + v1) //Typechecker should have caught this
      case StackLPair(e2) => {
        target = Eval(e2)
        push(StackRPair(v))
      }
      case StackRPair(v1) => target = Return(PairVal(v1, v))
      case StackInL => target = Return(InLVal(v))
      case StackInR => target = Return(InRVal(v))
      case StackCase(Nil) => throw new Exception("Empty set of rules?")
      case StackCase(Rule(p, b) :: rs) => {
        rules = rs
        matchVal = v
        body = b
        patternStack = Nil
        matchingTarget = Against(p, matchVal)

        while (!(matchingTarget.isInstanceOf[Binding] && patternStack.isEmpty)) {
          matchPattern
        }
        env = matchingTarget.asInstanceOf[Binding].b :: env
        target = Eval(body)
        push(PopFrame)
      }
      case StackFold => target = Return(FoldVal(v))
      case StackUnfold => v match {
        case FoldVal(v) => target = Return(v)
        case v => throw new Exception("Attempt to unfold a non-recursive value " + v) //typechecker should catch
      }
      case PopFrame => env = env.tail //'tail' should be safe, pops are added only with a frame
    }
  }

  sealed abstract class MatchingTarget
  case class Against(p : Pattern, v : Value) extends MatchingTarget
  case class Binding(b : Map[String, Value]) extends MatchingTarget

  var rules : List[Rule] = null //Rules as yet untried
  var matchVal : Value = null //Value being matched against
  var body : Expr = null //The body to be evaluated if the match succeeds
  var patternStack : List[PatStack] = null //The parts of the pattern still unmatched
  var matchingTarget : MatchingTarget = null //Either a pattern against a variable, or a binding being returned

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

  def evalDefn(m : Map[String, Value], d : Defn) : Map[String, Value] = d match {
    case ExprDefn(n, b, args) => m + (n -> runEval(Eval(b), List(m)))
    case TypeDefn(n, t) => m
  }

  def evaluate(p : Prog) : Value = runEval(Eval(p.e), List(p.defs.foldLeft(Map[String, Value]())(evalDefn)))

}