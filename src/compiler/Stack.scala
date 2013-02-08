package compiler

import model.{ Type, Pattern, Expr }

sealed abstract class Stack(name : String) {
  override def toString : String = name
}

case object SStk extends Stack("S(-)")
case class LetStk(n : String, b : Expr) extends Stack("let " + n + " = (-) in " + b)
case class ApStk(e2 : Expr) extends Stack("((-) " + e2 + ")")
case class Ap2Stk(x : String, b : Expr) extends Stack("((\\" + x + " . " + b + ") (-))")
case class PairrStk(e2 : Expr) extends Stack("((-) , " + e2 + ")")
case class Pairr2Stk(e1 : Expr) extends Stack("(" + e1 + " , (-))")
case object ProjLStk extends Stack("projL (-)")
case object ProjRStk extends Stack("projR (-)")
case object AbortStk extends Stack("abort (-)")
case object InLStk extends Stack("inL (-)")
case object InRStk extends Stack("inR (-)")
case class FoldStk(x : String) extends Stack("fold : " + x + " . (-)")
case object UnfoldStk extends Stack("unfold (-)")

sealed abstract class PatStack(name : String) {
  override def toString : String = name
}

case class PairPatStk(p2 : Pattern, e2 : Expr) extends PatStack("((-) , " + p2 + ") ~ ((-) , " + e2 + ")")
case class Pair2PatStk(bind1 : Map[String, Expr]) extends PatStack("(" + bind1 + " , (-))")
