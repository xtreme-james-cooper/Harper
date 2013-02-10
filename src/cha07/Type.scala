package cha07

sealed abstract class Type(name : String) {
  override def toString : String = name
}

case object NumTy extends Type("Nat")
case object StrTy extends Type("Str")
