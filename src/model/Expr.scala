package model

sealed abstract class Expr(name : String) {
  override def toString : String = name
}

case class Var(x : String) extends Expr(x)
case object Z extends Expr("Z")
case class S(e : Expr) extends Expr("S(" + e + ")")
case class Lam(x : String, t : Type, e : Expr) extends Expr("\\" + x + " : " + t + " . " + e)
case class Let(n : String, d : Expr, e : Expr) extends Expr("let " + n + " = " + d + " in " + e)
case class Ap(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + " " + e2 + ")")
case class Fix(x : String, t : Type, e : Expr) extends Expr("fix " + x + " : " + t + " in " + e)
case object Triv extends Expr("()")
case class Pairr(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + " , " + e2 + ")")
case class ProjL(e : Expr) extends Expr("projL " + e)
case class ProjR(e : Expr) extends Expr("projR " + e)
case class Abort(t : Type, e : Expr) extends Expr("abort : " + t + " " + e)
case class InL(t : Type, e : Expr) extends Expr("inL : " + t + " " + e)
case class InR(t : Type, e : Expr) extends Expr("inR : " + t + " " + e)
case class Match(e : Expr, rules : List[(Pattern, Expr)]) extends Expr(
  "case " + e + " of { " + rules.tail.foldLeft(rules.head._1 + " => " + rules.head._2)({ case (s, (p, e)) => s + "; " + p + " => " + e }) + " }")
case class Fold(x : String, t : Type, e : Expr) extends Expr("fold : " + x + " . " + t + " " + e)
case class Unfold(e : Expr) extends Expr("unfold " + e)
