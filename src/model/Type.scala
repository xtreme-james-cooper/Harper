package model

sealed abstract class Type(name : String) {
  override def toString : String = name
}

case object Nat extends Type("Nat")
case class Arr(t1 : Type, t2 : Type) extends Type("(" + t1 + " => " + t2 + ")")
case object Unitt extends Type("Unit")
case class Prod(t1 : Type, t2 : Type) extends Type("(" + t1 + " , " + t2 + ")")

