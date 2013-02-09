package all.interpreter

import all.model.{ Z, Var, Triv, S, ProjR, ProjL, Pairr, Lam, Fix, Expr, Ap }
import all.model.InR
import all.model.Match
import all.model.InL
import all.model.Abort
import all.model.SPat
import all.model.TrivPat
import all.model.InRPat
import all.model.PairPat
import all.model.InLPat
import all.model.VarPat
import all.model.WildPat
import all.model.ZPat
import all.model.Pattern
import Substitutor.subst
import all.model.Unfold
import all.model.Fold
import all.model.Let
import all.model.TLam
import all.model.TAp
import all.model.Raise
import all.model.UncaughtException
import all.model.Catch

object Evaluator {

  def eval : Expr => Expr = evalExpr

  private def evalExpr : Expr => Expr = {
    case Var(x)       => throw new Exception("unsubstituted variable " + x)
    case Z            => Z
    case S(e)         => evalExpr(e) match {
      case UncaughtException => UncaughtException
      case v => S(v)
    }
    case Lam(x, t, e) => Lam(x, t, e)
    case Let(n, d, b) => evalExpr(d) match {
      case UncaughtException => UncaughtException
      case v => evalExpr(subst(Map(n -> v))(b))
    }
    case Ap(e1, e2) => evalExpr(e1) match {
      case Lam(x, t, e) => evalExpr(e2) match {
        case UncaughtException => UncaughtException
        case v2 => evalExpr(subst(Map(x -> v2))(e))
      }
      case UncaughtException => UncaughtException
      case _            => throw new Exception("application of non-function " + e1)
    }
    case Fix(x, t, e)  => evalExpr(subst(Map(x -> Fix(x, t, e)))(e))
    case Triv          => Triv
    case Pairr(e1, e2) => evalExpr(e1) match {
      case UncaughtException => UncaughtException
      case v1 => evalExpr(e2) match {
        case UncaughtException => UncaughtException
        case v2 => Pairr(v1, v2)
      }
    }
    case ProjL(e) => evalExpr(e) match {
      case Pairr(e1, e2) => e1
      case UncaughtException => UncaughtException
      case _             => throw new Exception("projL of non-pair " + e)
    }
    case ProjR(e) => evalExpr(e) match {
      case Pairr(e1, e2) => e2
      case UncaughtException => UncaughtException
      case _             => throw new Exception("projR of non-pair " + e)
    }
    case Abort(t, e)   => evalExpr(e) match {
      case UncaughtException => UncaughtException
      case v => Abort(t, v)
    }
    case InL(t, e)     => evalExpr(e) match {
      case UncaughtException => UncaughtException
      case v => InL(t, v)
    }
    case InR(t, e)     => evalExpr(e) match {
      case UncaughtException => UncaughtException
      case v => InR(t, v)
    }
    case Match(e, rs)  => evalExpr(e) match {
      case UncaughtException => UncaughtException
      case v => evalRules(v)(rs)
    }
    case Fold(x, t, e) => evalExpr(e) match {
      case UncaughtException => UncaughtException
      case v => Fold(x, t, v)
    }
    case Unfold(e) => evalExpr(e) match {
      case Fold(x, t, e) => e
      case UncaughtException => UncaughtException
      case _             => throw new Exception("unfold of non-fold " + e)
    }
    case TLam(x, e) => evalExpr(e) //ignore types at runtime
    case TAp(e, t)  => evalExpr(e) //ignore types at runtime
    case Raise(t)   => UncaughtException
    case Catch(e1, e2) => evalExpr(e1) match {
      case UncaughtException => evalExpr(e2)
      case v                 => v
    }
    case UncaughtException => UncaughtException
  }

  private def evalRules(e : Expr) : List[(Pattern, Expr)] => Expr = {
    case Nil => UncaughtException
    case (p, b) :: rs => doMatch(p, e) match {
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