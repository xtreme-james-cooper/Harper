package cha07

sealed abstract class Expr(name : String) {
  override def toString : String = name
}

case class Var(x : String) extends Expr(x)
case class Num(n : Int) extends Expr(n.toString)
case class Str(s : String) extends Expr("\"" + s + "\"")
case class Plus(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + " + " + e2 + ")")
case class Times(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + " * " + e2 + ")")
case class Cat(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + " ^ " + e2 + ")")
case class Len(e : Expr) extends Expr("|" + e + "|")
case class Let(e1 : Expr, x : String, e2 : Expr) extends Expr("let " + x + " be " + e1 + " in " + e2 )
