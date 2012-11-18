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

object Evaluator {

  type Env = List[Map[String, Value]]

  type State = (Target, Env, List[Stack])

  sealed abstract class Target
  case class Eval(e : Expr) extends Target
  case class Return(v : Value) extends Target

  def getBinding(e : Env, x : String) : Value = e match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m(x)
    case m :: e                  => getBinding(e, x)
  }

  def flattenEnv(e : Env) : Map[String, Value] = e.foldRight(Map[String, Value]())({ case (m1, m2) => m2 ++ m1 })

  def eval : State => Value = {
    case (Eval(e), m, s) => e match {
      case Var(x)                   => eval(Return(getBinding(m, x)), m, s)
      case Z                        => eval(Return(ZVal), m, s)
      case S(n)                     => eval(Eval(n), m, StackS :: s)
      case Lam(v, t, e)             => eval(Return(LamVal(v, e, flattenEnv(m))), m, s)
      case App(e1, e2)              => eval(Eval(e1), m, StackLam(e2) :: s)
      case Fix(v, t, Lam(x, t2, e)) => eval(Eval(Lam(x, t2, e)), Map(v -> RecursiveLamVal(v, x, e, flattenEnv(m))) :: m, PopFrame :: s)
      case Fix(v, t, e)             => eval(Eval(e), m, s) //this will explode on CAFs (eg, recursive non-functions) so don't write them
      case Triv                     => eval(Return(TrivVal), m, s)
      case PairEx(e1, e2)           => eval(Eval(e1), m, StackLPair(e2) :: s)
      case InL(e, t)                => eval(Eval(e), m, StackInL :: s)
      case InR(e, t)                => eval(Eval(e), m, StackInR :: s)
      case Match(e, rs)             => eval(Eval(e), m, StackCase(rs) :: s)
    }
    case (Return(v), m, Nil) => v
    case (Return(v), m, stack :: s) => stack match {
      case StackS                       => eval(Return(SVal(v)), m, s)
      case StackLam(e2)                 => eval(Eval(e2), m, StackArg(v) :: s)
      case StackArg(LamVal(x, e, clos)) => eval(Eval(e), clos + (x -> v) :: m, PopFrame :: s)
      case StackArg(v1)                 => throw new Exception("Application of a non-function : " + v1) //Typechecker should have caught this
      case StackLPair(e2)               => eval(Eval(e2), m, StackRPair(v) :: s)
      case StackRPair(v1)               => eval(Return(PairVal(v1, v)), m, s)
      case StackInL                     => eval(Return(InLVal(v)), m, s)
      case StackInR                     => eval(Return(InRVal(v)), m, s)
      case StackCase(rs)                => matchRules(rs, v, m, s)
      case PopFrame                     => eval(Return(v), m.tail, s) //'tail' should be safe, pops are added only with a frame
    }
  }

  def matchRules : (List[Rule], Value, Env, List[Stack]) => Value = {
    case (Nil, v, m, s) => throw new Exception("No pattern match found for " + v)
    case (Rule(p, b) :: rs, v, m, s) => matchPattern(Nil, p, v) match {
      case None       => matchRules(rs, v, m, s)
      case Some(bind) => eval(Eval(b), bind :: m, PopFrame :: s)
    }
  }

  def matchPattern : (List[PatStack], Pattern, Value) => Option[Map[String, Value]] = {
    case (ps, WildPat, _)                       => matchStack(ps, Map())
    case (ps, VarPat(x), v)                     => matchStack(ps, Map(x -> v))
    case (ps, ZPat, ZVal)                       => matchStack(ps, Map())
    case (ps, SPat(p), SVal(v))                 => matchPattern(ps, p, v)
    case (ps, TrivPat, TrivVal)                 => matchStack(ps, Map())
    case (ps, InLPat(p), InLVal(v))             => matchPattern(ps, p, v)
    case (ps, InRPat(p), InRVal(v))             => matchPattern(ps, p, v)
    case (ps, PairPat(p1, p2), PairVal(v1, v2)) => matchPattern(PatStackLPair(v2, p2) :: ps, p1, v1)
    case _                                      => None
  }

  def matchStack : (List[PatStack], Map[String, Value]) => Option[Map[String, Value]] = {
    case (Nil, m) => Some(m)
    case (PatStackLPair(v2, p2) :: ps, m) => matchPattern(PatStackRPair(m) :: ps, p2, v2)
    case (PatStackRPair(m1) :: ps, m2) if (m1.keySet & m2.keySet).isEmpty => matchStack(ps, m1 ++ m2)
    case (PatStackRPair(m1) :: ps, m2) => throw new Exception("Patterns cannot have repeated variables") //genuine error; as of now, no way to check
  }

  def evalDefn(d : Defn, m : Map[String, Value]) : Map[String, Value] = m + (d.name -> eval(Eval(d.body), List(m), Nil))

  def evaluate(p : Prog) : Value = eval(Eval(p.e), List(p.defs.foldRight(Map[String, Value]())(evalDefn)), Nil)

}