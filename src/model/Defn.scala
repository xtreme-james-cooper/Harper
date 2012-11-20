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

class Prog(val defs : List[Defn], val e : Expr) {
  override def toString : String = defs.foldLeft("")({ case (s, defn) => s + defn }) + e
}