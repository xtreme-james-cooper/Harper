package model

sealed abstract class Type(name : String) {
  override def toString : String = name
}

case object Nat extends Type("Nat")
case class Arr(t1 : Type, t2 : Type) extends Type("(" + t1 + " => " + t2 + ")")
case object Unitt extends Type("Unit")
case class Prod(t1 : Type, t2 : Type) extends Type("(" + t1 + " , " + t2 + ")")
case object Voidd extends Type("Void")
case class Sum(t1 : Type, t2 : Type) extends Type("(" + t1 + " + " + t2 + ")")
case class TyVar(x : String) extends Type(x)
case class Rec(x : String, t : Type) extends Type("mu " + x + " . " + t)
