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

object Evaluator {

  def evalExpr(s : List[Stack], e : Expr) : Expr = (s, e) match {
    case (s, Var(x))         => throw new Exception("Unbound identifier : " + x)
    case (s, Z)              => evalStack(s, Z)
    case (s, S(n))           => evalExpr(StackS :: s, n)
    case (s, Lam(v, t, e))   => evalStack(s, Lam(v, t, e))
    case (s, App(e1, e2))    => evalExpr(StackApp(e2) :: s, e1)
    case (s, Fix(v, t, e))   => evalExpr(s, e.replace(v, Fix(v, t, e)))
    case (s, Triv)           => evalStack(s, Triv)
    case (s, PairEx(e1, e2)) => evalExpr(StackLPair(e2) :: s, e1)
    case (s, InL(e, t))      => evalExpr(StackInL :: s, e)
    case (s, InR(e, t))      => evalExpr(StackInR :: s, e)
    case (s, Match(e, rs))   => evalExpr(StackCase(rs) :: s, e)
  }

  def evalStack : (List[Stack], Expr) => Expr = {
    case (Nil, e)                          => e
    case (StackS :: s, e)                  => evalStack(s, S(e))
    case (StackApp(e2) :: s, Lam(v, t, e)) => evalExpr(s, e.replace(v, e2))
    case (StackLPair(e2) :: s, e)          => evalExpr(StackRPair(e) :: s, e2)
    case (StackRPair(e1) :: s, e)          => evalStack(s, PairEx(e1, e))
    case (StackInL :: s, e)                => evalStack(s, InL(e, UnitTy))
    case (StackInR :: s, e)                => evalStack(s, InR(e, UnitTy))
    case (StackCase(rs) :: s, e)           => matchRules(e)(rs)(s)
  }

  def matchRules(e : Expr)(rs : List[Rule])(s : List[Stack]) : Expr = (e, rs) match {
    case (e, Nil) => throw new Exception("No pattern match found for " + e)
    case (e, Rule(p, b) :: rs) => matchPattern(e, p) match {
      case None       => matchRules(e)(rs)(s)
      case Some(bind) => evalExpr(s, b.replace(bind))
    }
  }

  def matchPattern : (Expr, Pattern) => Option[Map[String, Expr]] = {
    case (_, WildPat)           => Some(Map())
    case (e, VarPat(x))         => Some(Map(x -> e))
    case (Z, ZPat)              => Some(Map())
    case (S(e), SPat(p))        => matchPattern(e, p)
    case (Triv, TrivPat)        => Some(Map())
    case (InL(e, t), InLPat(p)) => matchPattern(e, p)
    case (InR(e, t), InRPat(p)) => matchPattern(e, p)
    case (PairEx(e1, e2), PairPat(p1, p2)) => matchPattern(e1, p1) match {
      case Some(b1) => matchPattern(e2, p2) match {
        case Some(b2) => Some(b1 ++ b2)
        case None     => None
      }
      case None => None
    }
    case _ => None
  }
  
  def evaluate(p : Prog) : Expr = evalExpr(Nil, p.defs.foldRight(p.e)({ case (Defn(n, b), expr) => expr.replace(n, b) }))

}