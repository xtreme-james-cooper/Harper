package all.compiler

import all.model.{ Type, Pattern, Expr }

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
case class MatchStk(rs : List[(Pattern, Expr)]) extends Stack("case (-) of " + rs)
case class FoldStk(x : String) extends Stack("fold : " + x + " . (-)")
case object UnfoldStk extends Stack("unfold (-)")
case class CatchStk(e2 : Expr) extends Stack("try (-) catch " + e2)
case class PatStkRules(e : Expr, b : Expr, rs : List[(Pattern, Expr)]) extends Stack("(-) ~ " + e + " --> " + b + " || " + rs)
case class PairPatStk(p2 : Pattern, e2 : Expr) extends Stack("((-) , " + p2 + ") ~ ((-) , " + e2 + ")")
case class Pair2PatStk(bind1 : Map[String, Expr]) extends Stack("(" + bind1 + " , (-))")
