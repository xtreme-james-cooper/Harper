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

  def evalExpr(m : Map[String, Value])(s : List[Stack], e : Expr) : Value = (s, e) match {
    case (s, Var(x)) if m.contains(x) => m(x)
    case (s, Var(x))                  => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case (s, Z)                       => evalStack(m)(s, ZVal)
    case (s, S(n))                    => evalExpr(m)(StackS :: s, n)
    case (s, Lam(v, t, e))            => evalStack(m)(s, LamVal(v, e))
    case (s, App(e1, e2))             => evalExpr(m)(StackLam(e2) :: s, e1)
    case (s, Fix(v, t, e))            => evalExpr(m + (v -> Fix(v, t, e)))(s, e)
    case (s, Triv)                    => evalStack(m)(s, TrivVal)
    case (s, PairEx(e1, e2))          => evalExpr(m)(StackLPair(e2) :: s, e1)
    case (s, InL(e, t))               => evalExpr(m)(StackInL :: s, e)
    case (s, InR(e, t))               => evalExpr(m)(StackInR :: s, e)
    case (s, Match(e, rs))            => evalExpr(m)(StackCase(rs) :: s, e)
  }

  def evalStack(m : Map[String, Value]) : (List[Stack], Value) => Value = {
    case (Nil, v)                           => v
    case (StackS :: s, v)                   => evalStack(m)(s, SVal(v))
    case (StackLam(e2) :: s, v)             => evalExpr(m)(StackArg(v) :: s, e2)
    case (StackArg(LamVal(v1, e)) :: s, v2) => evalExpr(m + (v1 -> v2))(s, e)
    case (StackArg(v1) :: s, v2)            => throw new Exception("Application of a non-function : " + v1) //Typechecker should get this
    case (StackLPair(e2) :: s, v)           => evalExpr(m)(StackRPair(v) :: s, e2)
    case (StackRPair(v1) :: s, v)           => evalStack(m)(s, PairVal(v1, v))
    case (StackInL :: s, v)                 => evalStack(m)(s, InLVal(v))
    case (StackInR :: s, v)                 => evalStack(m)(s, InRVal(v))
    case (StackCase(rs) :: s, v)            => matchRules(m)(v)(rs)(s)
  }

  def matchRules(m : Map[String, Value])(e : Value)(rs : List[Rule])(s : List[Stack]) : Value = (e, rs) match {
    case (e, Nil) => throw new Exception("No pattern match found for " + e)
    case (e, Rule(p, b) :: rs) => matchPattern(Nil, e, p) match {
      case None       => matchRules(m)(e)(rs)(s)
      case Some(bind) => evalExpr(m ++ bind)(s, b)
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
    case (PatStackRPair(m1) :: s, m2) => throw new Exception("Patterns cannot have repeated variables")
  }

  def evaluate(p : Prog) : Value = evalExpr(p.defs.foldRight(Map[String, Value]())({ case (Defn(n, b), m) => m + (n -> evalExpr(m)(Nil, b)) }))(Nil, p.e)

}