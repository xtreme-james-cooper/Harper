package cha12

sealed abstract class Type(name : String) {
  override def toString : String = name
}

case object NumTy extends Type("Nat")
case class ArrTy(t1 : Type, t2 : Type) extends Type("(" + t1 + " -> " + t2 + ")")
case class ProdTy(t1 : Type, t2 : Type) extends Type("(" + t1 + ", " + t2 + ")")
case object UnitTy extends Type("Unit")
case object VoidTy extends Type("Void")
case class SumTy(t1 : Type, t2 : Type) extends Type("(" + t1 + " + " + t2 + ")")