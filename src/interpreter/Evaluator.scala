package interpreter

import model.{ ZVal, Z, S, Expr, Value, SVal }

object Evaluator {

  def eval : Expr => Value = {
    case Z    => ZVal
    case S(e) => SVal(eval(e))
  }

}