package model

sealed abstract class Expr(name : String) {
  override def toString : String = name
}

case object Z extends Expr("Z")
case class S(e : Expr) extends Expr("S(" + e + ")")
