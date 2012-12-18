package interpreter

import model.{ Z, Var, Triv, S, ProjR, ProjL, Pairr, Lam, Fix, Expr, Ap }
import model.InR
import model.Match
import model.InL
import model.Abort
import model.SPat
import model.TrivPat
import model.InRPat
import model.PairPat
import model.InLPat
import model.VarPat
import model.WildPat
import model.ZPat
import model.Pattern
import Substitutor.subst
import model.Unfold
import model.Fold

object Evaluator {

  def eval : Expr => Expr = evalExpr

  private def evalExpr : Expr => Expr = {
    case Var(x)       => throw new Exception("unsubstituted variable " + x)
    case Z            => Z
    case S(e)         => S(evalExpr(e))
    case Lam(x, t, e) => Lam(x, t, e)
    case Ap(e1, e2) => evalExpr(e1) match {
      case Lam(x, t, e) => evalExpr(subst(Map(x -> evalExpr(e2)))(e))
      case _            => throw new Exception("application of non-function " + e1)
    }
    case Fix(x, t, e)  => evalExpr(subst(Map(x -> Fix(x, t, e)))(e))
    case Triv          => Triv
    case Pairr(e1, e2) => Pairr(evalExpr(e1), evalExpr(e2))
    case ProjL(e) => evalExpr(e) match {
      case Pairr(e1, e2) => e1
      case _             => throw new Exception("projL of non-pair " + e)
    }
    case ProjR(e) => evalExpr(e) match {
      case Pairr(e1, e2) => e2
      case _             => throw new Exception("projR of non-pair " + e)
    }
    case Abort(t, e)   => Abort(t, evalExpr(e))
    case InL(t, e)     => InL(t, evalExpr(e))
    case InR(t, e)     => InR(t, evalExpr(e))
    case Match(e, rs)  => evalRules(e)(rs)
    case Fold(x, t, e) => Fold(x, t, eval(e))
    case Unfold(e)     => eval(e) match {
      case Fold(x, t, e) => e
      case _ => throw new Exception("unfold of non-fold " + e)
    }
  }

  private def evalRules(e : Expr) : List[(Pattern, Expr)] => Expr = {
    case Nil => throw new Exception("no match found for " + e)
    case (p, b) :: rs => doMatch(p, evalExpr(e)) match {
      case None       => evalRules(e)(rs)
      case Some(bind) => evalExpr(subst(bind)(b))
    }
  }

  private def doMatch : (Pattern, Expr) => Option[Map[String, Expr]] = {
    case (WildPat, _)    => Some(Map())
    case (VarPat(x), e)  => Some(Map(x -> e))
    case (TrivPat, Triv) => Some(Map())
    case (PairPat(p1, p2), Pairr(e1, e2)) =>
      for {
        b1 <- doMatch(p1, e1)
        b2 <- doMatch(p2, e2)
      } yield b1 ++ b2
    case (InLPat(p), InL(t, e)) => doMatch(p, e)
    case (InRPat(p), InR(t, e)) => doMatch(p, e)
    case (ZPat, Z)              => Some(Map())
    case (SPat(p), S(e))        => doMatch(p, e)
    case _                      => None
  }

}