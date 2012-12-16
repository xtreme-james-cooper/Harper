package model

sealed abstract class Expr(name : String) {
  override def toString : String = name
}

case class Var(x : String) extends Expr(x)
case object Z extends Expr("Z")
case class S(e : Expr) extends Expr("S(" + e + ")")
case class IfZ(e : Expr, ez : Expr, x : String, es : Expr) extends Expr("ifz " + e + " { Z => " + ez + " ; S(" + x + ") => " + es + " }")
case class Lam(x : String, t : Type, e : Expr) extends Expr("\\" + x + " : " + t + " . " + e)
case class Ap(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + " " + e2 + ")")
case class Fix(x : String, t : Type, e : Expr) extends Expr("fix " + x + " : " + t + " in " + e)
