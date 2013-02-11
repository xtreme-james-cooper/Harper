package cha09

sealed abstract class Expr(name : String) {
  override def toString : String = name
}

case class Var(x : String) extends Expr(x)
case object Z extends Expr("Z")
case class S(n : Expr) extends Expr("S(" + n + ")")
case class Let(e1 : Expr, x : String, e2 : Expr) extends Expr("let " + x + " be " + e1 + " in " + e2)
case class Ap(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + " " + e2 + ")")
case class Lam(t : Type, x : String, e : Expr) extends Expr("\\" + x + ":" + t + " . " + e)
case class Rec(e0 : Expr, x : String, y : String, e1 : Expr, e : Expr) extends Expr(
    "rec " + e + " { Z => " + e0 + " | S(" + x + ") with " + y + " => " + e1 + " }") 