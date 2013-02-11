package cha11

sealed abstract class Expr(name : String) {
  override def toString : String = name
}

case class Var(x : String) extends Expr(x)
case object Z extends Expr("Z")
case class S(n : Expr) extends Expr("S(" + n + ")")
case class Let(e1 : Expr, x : String, e2 : Expr) extends Expr("let " + x + " be " + e1 + " in " + e2)
case class Ap(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + " " + e2 + ")")
case class Lam(t : Type, x : String, e : Expr) extends Expr("\\" + x + ":" + t + " . " + e)
case class Fix(t : Type, x : String, e : Expr) extends Expr("fix " + x + " : " + t + " is " + e) 
case class IfZ(e : Expr, e0 : Expr, x : String, e1 : Expr) extends Expr("ifz " + e + " { 0 => " + e0 + " | S(" + x + ") => " + e1 + " }") 
case class Pair(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + ", "+ e2 + ")")
case class PrL(e : Expr) extends Expr("projl " + e)
case class PrR(e : Expr) extends Expr("projr " + e)
case object Triv extends Expr("()")