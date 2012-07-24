package model

sealed abstract class Type(name : String) {
  override def toString : String = name
  def replace(n : String, t : Type) : Type
  def replace(syns : Map[String, Type]) : Type = syns.foldRight(this)({case ((n, t), typ) => typ.replace(n, t)})
}

case object Nat extends Type("Nat") {
  override def replace(n : String, t : Type) : Type = this
}

case class Arrow(t1 : Type, t2 : Type) extends Type("(" + t1 + " -> " + t2 + ")") {
  override def replace(n : String, t : Type) : Type = Arrow(t1.replace(n, t), t2.replace(n, t))
}

case object UnitTy extends Type("Unit") {
  override def replace(n : String, t : Type) : Type = this
}

case class Product(t1 : Type, t2 : Type) extends Type("(" + t1 + ", " + t2 + ")") {
  override def replace(n : String, t : Type) : Type = Product(t1.replace(n, t), t2.replace(n, t))
}

case class Sum(t1 : Type, t2 : Type) extends Type("(" + t1 + " + " + t2 + ")") {
  override def replace(n : String, t : Type) : Type = Sum(t1.replace(n, t), t2.replace(n, t))
}

class TyName(n : String) extends Type(n) {
  override def replace(vbl : String, t : Type) : Type = if (vbl == n) t else this
}