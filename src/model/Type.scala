package model

sealed abstract class Type(name : String) {
  override def toString : String = name
}

case object Nat extends Type("Nat")
