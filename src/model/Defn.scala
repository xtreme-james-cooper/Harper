package model

case class Defn(name : String, body : Expr) {

  override def toString : String = name + " = " + body + "\n"

  def this(name : String, args : List[(String, Type)], t : Type, e : Expr) =
    this(name,
      Fix(name,
        args.foldRight(t)({ case ((v, ty), typ) => Arrow(ty, typ) }),
        args.foldRight(e)({ case ((v, ty), ex) => Lam(v, ty, ex) })))

}

class Prog(val defs : List[Defn], val e : Expr) {
  override def toString : String = defs.foldLeft("")({ case (s, defn) => s + defn }) + e
}