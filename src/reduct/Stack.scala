package reduct

import model.Expr
import model.Rule
import model.Pattern
import model.Value

sealed abstract class Stack(name : String) {
  override def toString : String = name
}

case object StackS extends Stack("S(-)")
case class StackLam(e2 : Expr) extends Stack("((-) " + e2 + ")")
case class StackArg(v1 : Value) extends Stack("(" + v1 + ", (-))")
case class StackLPair(e2 : Expr) extends Stack("((-), " + e2 + ")")
case class StackRPair(v1 : Value) extends Stack("(" + v1 + ", (_))")
case object StackInL extends Stack("inl (-)")
case object StackInR extends Stack("inr (-)")
case class StackCase(rs : List[Rule]) extends Stack("case (-) of { " + rs.foldRight("")({ case (r1, r2) => r1 + " | " + r2 }) + "}")
case object StackUnfold extends Stack("unfold (-)")
case object StackFold extends Stack("fold (-)")
case object PopFrame extends Stack(" ! ")

sealed abstract class PatStack(name : String) {
  override def toString : String = name
}

case class PatStackLPair(v2 : Value, p2 : Pattern) extends PatStack("((-), " + v2 + ") ~ ((-), " + p2 + ")")
case class PatStackRPair(m : Map[String, Value]) extends PatStack("(" + m + ", (-))")