package model

sealed abstract class Type(name : String) {
  override def toString : String = name
}

case object Nat extends Type("Nat")
case class Arrow(t1 : Type, t2 : Type) extends Type("(" + t1 + " -> " + t2 + ")")
case object UnitTy extends Type("Unit")
case class Product(t1 : Type, t2 : Type) extends Type("(" + t1 + ", " + t2 + ")")
case class Sum(t1 : Type, t2 : Type) extends Type("(" + t1 + " + " + t2 + ")")
