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

object Evaluator {

  type Env = List[Map[String, Value]]

  def getBinding(e : Env, x : String) : Value = e match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m(x)
    case m :: e                  => getBinding(e, x)
  }

  def flattenEnv(e : Env) : Map[String, Value] = e.foldRight(Map[String, Value]())({ case (m1, m2) => m2 ++ m1 })

  def evalExpr : (Expr, Env, List[Stack]) => Value = {
    case (Var(x), m, s)                   => evalStack(getBinding(m, x), m, s)
    case (Z, m, s)                        => evalStack(ZVal, m, s)
    case (S(n), m, s)                     => evalExpr(n, m, StackS :: s)
    case (Lam(v, t, e), m, s)             => evalStack(LamVal(v, e, flattenEnv(m)), m, s)
    case (App(e1, e2), m, s)              => evalExpr(e1, m, StackLam(e2) :: s)
    //Currently a hack; it only works on top-level functions. Fortunately the user can't write fixpoints manually
    case (Fix(v, t, Lam(x, t2, e)), m, s) => evalExpr(Lam(x, t2, e), Map(v -> LamVal(x, e, flattenEnv(m))) :: m, PopFrame :: s)
    //this will explode on CAFs (eg, recursive non-functions) so don't write them either
    case (Fix(v, t, e), m, s)             => evalExpr(e, m, s)
    case (Triv, m, s)                     => evalStack(TrivVal, m, s)
    case (PairEx(e1, e2), m, s)           => evalExpr(e1, m, StackLPair(e2) :: s)
    case (InL(e, t), m, s)                => evalExpr(e, m, StackInL :: s)
    case (InR(e, t), m, s)                => evalExpr(e, m, StackInR :: s)
    case (Match(e, rs), m, s)             => evalExpr(e, m, StackCase(rs) :: s)
  }

  def evalStack : (Value, Env, List[Stack]) => Value = {
    case (v, m, Nil)                               => v
    case (v, m, StackS :: s)                       => evalStack(SVal(v), m, s)
    case (v, m, StackLam(e2) :: s)                 => evalExpr(e2, m, StackArg(v) :: s)
    case (v, m, StackArg(LamVal(x, e, clos)) :: s) => evalExpr(e, clos + (x -> v) :: m, PopFrame :: s)
    case (v, m, StackArg(v1) :: s)                 => throw new Exception("Application of a non-function : " + v1) //Typechecker should have caught this
    case (v, m, StackLPair(e2) :: s)               => evalExpr(e2, m, StackRPair(v) :: s)
    case (v, m, StackRPair(v1) :: s)               => evalStack(PairVal(v1, v), m, s)
    case (v, m, StackInL :: s)                     => evalStack(InLVal(v), m, s)
    case (v, m, StackInR :: s)                     => evalStack(InRVal(v), m, s)
    case (v, m, StackCase(rs) :: s)                => matchRules(rs, v, m, s)
    case (v, f :: m, PopFrame :: s)                => evalStack(v, m, s)
    case (v, Nil, PopFrame :: s)                   => throw new Exception("Too few stack frames?") //Should never happen, pops are added only with a frame
  }

  def matchRules : (List[Rule], Value, Env, List[Stack]) => Value = {
    case (Nil, v, m, s) => throw new Exception("No pattern match found for " + v)
    case (Rule(p, b) :: rs, v, m, s) => matchPattern(Nil, v, p) match {
      case None       => matchRules(rs, v, m, s)
      case Some(bind) => evalExpr(b, bind :: m, PopFrame :: s)
    }
  }

  def matchPattern : (List[PatStack], Value, Pattern) => Option[Map[String, Value]] = {
    case (s, _, WildPat)                       => matchStack(s, Map())
    case (s, v, VarPat(x))                     => matchStack(s, Map(x -> v))
    case (s, ZVal, ZPat)                       => matchStack(s, Map())
    case (s, SVal(v), SPat(p))                 => matchPattern(s, v, p)
    case (s, TrivVal, TrivPat)                 => matchStack(s, Map())
    case (s, InLVal(v), InLPat(p))             => matchPattern(s, v, p)
    case (s, InRVal(v), InRPat(p))             => matchPattern(s, v, p)
    case (s, PairVal(v1, v2), PairPat(p1, p2)) => matchPattern(PatStackLPair(v2, p2) :: s, v1, p1)
    case _                                     => None
  }

  def matchStack : (List[PatStack], Map[String, Value]) => Option[Map[String, Value]] = {
    case (Nil, m) => Some(m)
    case (PatStackLPair(e2, p2) :: s, m) => matchPattern(PatStackRPair(m) :: s, e2, p2)
    case (PatStackRPair(m1) :: s, m2) if (m1.keySet & m2.keySet).isEmpty => matchStack(s, m1 ++ m2)
    case (PatStackRPair(m1) :: s, m2) => throw new Exception("Patterns cannot have repeated variables") //genuine error; as of now, no way to check
  }

  def evalDefn(d : Defn, m : Map[String, Value]) : Map[String, Value] = {
    println("new defn")
    m + (d.name -> evalExpr(d.body, List(m), Nil))
  }

  def evaluate(p : Prog) : Value = evalExpr(p.e, List(p.defs.foldRight(Map[String, Value]())(evalDefn)), Nil)

}