package model

case class Rule(p : Pattern, b : Expr) {
  override def toString : String = p + " -> " + b
}