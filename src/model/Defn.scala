package model

sealed abstract class Defn(name : String) {
  override def toString : String = name
}

case class ExprDefn(name : String, body : Expr) extends Defn(name + " = " + body + "\n") {

  def this(name : String, args : List[(String, Type)], t : Type, e : Expr) =
    this(name,
      Fix(name,
        args.foldRight(t)({ case ((v, ty), typ) => Arrow(ty, typ) }),
        args.foldRight(e)({ case ((v, ty), ex) => Lam(v, ty, ex) })))

}

case class TypeDefn(val name : String, val t : Type) extends Defn(name + " = " + t + "\n")