package interpreter

import Substitutor.subst
import model.{LamVal, Lam, Fix, Ap, IfZ, ZVal, Z, S, Expr, Value, SVal, Var}

object Evaluator {

  def eval : Expr => Value = {
    case Var(x) => throw new Exception("unsubstituted variable " + x)
    case Z      => ZVal
    case S(e)   => SVal(eval(e))
    case IfZ(e, ez, x, es) => eval(e) match {
      case ZVal    => eval(ez)
      case SVal(n) => eval(subst(x, n.exprify)(es))
      case _ => throw new Exception("ifz of non-num " + e)
    }
    case Lam(x, t, e) => LamVal(x, t, e)
    case Ap(e1, e2) => eval(e1) match {
      case LamVal(x, t, e) => eval(subst(x, eval(e2).exprify)(e))
      case _ => throw new Exception("application of non-function " + e1)
    }
    case Fix(x, t, e) => eval(subst(x, Fix(x, t, e))(e))
  }

}