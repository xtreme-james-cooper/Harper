package compiler

import model.{ Value, Rule, Expr }

sealed abstract class ExprStack(name : String) {
  override def toString : String = name
}

case object StackS extends ExprStack("S(-)")
case class StackLam(e2 : Expr) extends ExprStack("((-) " + e2 + ")")
case class StackArg(v1 : Value) extends ExprStack("(" + v1 + ", (-))")
case class StackLPair(e2 : Expr) extends ExprStack("((-), " + e2 + ")")
case class StackRPair(v1 : Value) extends ExprStack("(" + v1 + ", (_))")
case object StackInL extends ExprStack("inl (-)")
case object StackInR extends ExprStack("inr (-)")
case class StackCase(rs : List[Rule]) extends ExprStack("case (-) of { " + rs.foldRight("")({ case (r1, r2) => r1 + " | " + r2 }) + "}")
case object StackUnfold extends ExprStack("unfold (-)")
case object StackFold extends ExprStack("fold (-)")
case class StackHandler(e2 : Expr) extends ExprStack("try (-) catch " + e2)
case object PopFrame extends ExprStack(" ! ")

