package interpreter

import Substitutor.subst
import model.{ Z, Var, Triv, S, ProjR, ProjL, Pairr, Lam, IfZ, Fix, Expr, Ap }

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
  }

  def isVal : Expr => Boolean = {
    case Z             => true
    case S(e)          => isVal(e)
    case Lam(x, t, e)  => true
    case Triv          => true
    case Pairr(e1, e2) => isVal(e1) && isVal(e2)
    case _             => false
  }

}