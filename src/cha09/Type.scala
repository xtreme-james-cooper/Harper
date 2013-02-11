package cha09

sealed abstract class Type(name : String) {
  override def toString : String = name
}

case object NumTy extends Type("Nat")
case class ArrTy(t1 : Type, t2 : Type) extends Type("(" + t1 + " -> " + t2 + ")")