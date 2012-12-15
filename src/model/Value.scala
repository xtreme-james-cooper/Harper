package model

sealed abstract class Value(name : String) {
  override def toString : String = name
}

case object ZVal extends Value("Z")
case class SVal(e : Value) extends Value("S(" + e + ")")