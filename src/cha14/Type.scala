package cha14

sealed abstract class Type(name : String) {
  override def toString : String = name
}

case class VarTy(t : String) extends Type(t)
case object NumTy extends Type("Num")
case class ArrTy(t1 : Type, t2 : Type) extends Type("(" + t1 + " -> " + t2 + ")")
case class ProdTy(t1 : Type, t2 : Type) extends Type("(" + t1 + ", " + t2 + ")")
case object UnitTy extends Type("Unit")
case object VoidTy extends Type("Void")
case class SumTy(t1 : Type, t2 : Type) extends Type("(" + t1 + " + " + t2 + ")")