package model

sealed abstract class Value(name : String, val exprify : Expr) {
  override def toString : String = name
}

case object ZVal extends Value("Z", Z)
case class SVal(e : Value) extends Value("S(" + e + ")", S(e.exprify))