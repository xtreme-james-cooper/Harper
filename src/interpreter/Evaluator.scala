package interpreter

import Substitutor.subst
import model.{ IfZ, ZVal, Z, S, Expr, Value, SVal, Var }

object Evaluator {

  def eval : Expr => Value = {
    case Var(x) => throw new Exception("unsubstituted variable " + x)
    case Z      => ZVal
    case S(e)   => SVal(eval(e))
    case IfZ(e, ez, x, es) => eval(e) match {
      case ZVal    => eval(ez)
      case SVal(n) => eval(subst(x, n.exprify)(es))
    }
  }

}