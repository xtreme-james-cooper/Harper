package interpreter

import Substitutor.subst
import model.{ Z, Var, Triv, S, ProjR, ProjL, Pairr, Lam, IfZ, Fix, Expr, Ap }
import model.InR
import model.Case
import model.InL
import model.Abort

object Evaluator {

  def eval : Expr => Expr = {
    case Var(x) => throw new Exception("unsubstituted variable " + x)
    case Z      => Z
    case S(e)   => S(eval(e))
    case IfZ(e, ez, x, es) => eval(e) match {
      case Z    => eval(ez)
      case S(n) => eval(subst(x, n)(es))
      case _    => throw new Exception("ifz of non-num " + e)
    }
    case Lam(x, t, e) => Lam(x, t, e)
    case Ap(e1, e2) => eval(e1) match {
      case Lam(x, t, e) => eval(subst(x, eval(e2))(e))
      case _            => throw new Exception("application of non-function " + e1)
    }
    case Fix(x, t, e)  => eval(subst(x, Fix(x, t, e))(e))
    case Triv          => Triv
    case Pairr(e1, e2) => Pairr(eval(e1), eval(e2))
    case ProjL(e) => eval(e) match {
      case Pairr(e1, e2) => e1
      case _             => throw new Exception("projL of non-pair " + e)
    }
    case ProjR(e) => eval(e) match {
      case Pairr(e1, e2) => e2
      case _             => throw new Exception("projR of non-pair " + e)
    }
    case Abort(t, e)             => Abort(t, eval(e))
    case InL(t, e)               => InL(t, eval(e))
    case InR(t, e)               => InR(t, eval(e))
    case Case(e, x1, e1, x2, e2) => eval(e) match {
      case InL(t, e) => eval(subst(x1, e)(e1))
      case InR(t, e) => eval(subst(x2, e)(e2))
      case _ => throw new Exception("case of non-sum " + e)
    }
  }

  def isVal : Expr => Boolean = {
    case Z             => true
    case S(e)          => isVal(e)
    case Lam(x, t, e)  => true
    case Triv          => true
    case Pairr(e1, e2) => isVal(e1) && isVal(e2)
    case InL(t, e)        => isVal(e)
    case InR(t, e)        => isVal(e)
    case _             => false
  }

}