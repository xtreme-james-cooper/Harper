package reduct

import model.Expr
import model.Rule
import model.Pattern

sealed abstract class Stack(name : String) {
  override def toString : String = name
}

case object StackS extends Stack("S(-)")
case class StackApp(e2 : Expr) extends Stack("((-) " + e2 + ")")
case class StackLPair(e2 : Expr) extends Stack("(-), " + e2 + ")")
case class StackRPair(e1 : Expr) extends Stack("(" + e1 + ", (_))")
case object StackInL extends Stack("inl (-)")
case object StackInR extends Stack("inr (_)")
case class StackCase(rs : List[Rule]) extends Stack("case (-) of { " + rs.foldRight("")({ case (r1, r2) => r1 + " | " + r2 }) + "}")
