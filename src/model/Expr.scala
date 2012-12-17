package model

sealed abstract class Expr(name : String) {
  override def toString : String = name
}

case class Var(x : String) extends Expr(x)
case object Z extends Expr("Z")
case class S(e : Expr) extends Expr("S(" + e + ")")
case class IfZ(e : Expr, ez : Expr, x : String, es : Expr) extends Expr("ifz " + e + " { Z => " + ez + " ; S(" + x + ") => " + es + " }")
case class Lam(x : String, t : Type, e : Expr) extends Expr("\\" + x + " : " + t + " . " + e)
case class Ap(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + " " + e2 + ")")
case class Fix(x : String, t : Type, e : Expr) extends Expr("fix " + x + " : " + t + " in " + e)
case object Triv extends Expr("()")
case class Pairr(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + " , " + e2 + ")")
case class ProjL(e : Expr) extends Expr("projL " + e)
case class ProjR(e : Expr) extends Expr("projR " + e)
case class Abort(t : Type, e : Expr) extends Expr("abort : " + t + " " + e)
case class InL(t : Type, e : Expr) extends Expr("inL : " + t + " " + e)
case class InR(t : Type, e : Expr) extends Expr("inR : " + t + " " + e)
case class Case(e : Expr, x1 : String, e1 : Expr, x2 : String, e2 : Expr) extends Expr(
  "case " + e + " { inL " + x1 + " => " + e1 + " ; inR " + x2 + " => " + e2 + " }")


