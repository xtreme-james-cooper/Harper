package model

sealed abstract class Defn(name : String) {
  override def toString : String = name
}

case class ExprDefn(name : String, body : Expr, args : List[(String, Type)]) extends Defn(name + " = " + body + "\n") {

  def this(name : String, args : List[(String, Type)], t : Type, e : Expr) =
    this(name,
      Fix(name, args.foldRight(e)({ case ((v, ty), ex) => Lam(v, ty, ex) })),
      (name -> args.foldRight(t)({ case ((v, ty), typ) => Arrow(ty, typ) })) :: args)

}

case class TypeDefn(name : String, body : Type) extends Defn("type " + name + " = " + body + "\n")

object Prog {

  val builtinDefs : List[Defn] = List(
    TypeDefn("Unit", UnitTy),
    TypeDefn("Nat", Nat),
    TypeDefn("Bool", Sum(UnitTy, UnitTy)),
    new ExprDefn("true", Nil, TyVar("Bool"), InL(Triv)),
    new ExprDefn("false", Nil, TyVar("Bool"), InR(Triv)))

}

class Prog(newDefs : List[Defn], val e : Command) {

  val defs = Prog.builtinDefs ++ newDefs

  override def toString : String = defs.foldLeft("")({ case (s, defn) => s + defn }) + e
}
