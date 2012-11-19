package model

sealed abstract class Expr(name : String) {
  override def toString : String = name
}

case class Var(v : String) extends Expr(v)
case object Z extends Expr("Z")
case class S(e : Expr) extends Expr("S(" + e + ")")
case class Lam(v : String, t : Type, e : Expr) extends Expr("\\" + v + " . " + e)
case class App(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + " " + e2 + ")")
case class Fix(v : String, t : Type, e : Expr) extends Expr("fix " + v + " in " + e)
case object Triv extends Expr("()")
case class PairEx(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + ", " + e2 + ")")
case class InL(i : Expr, t : Type) extends Expr("inl " + i)
case class InR(i : Expr, t : Type) extends Expr("inr " + i)
case class Match(t : Expr, rules : List[Rule]) extends Expr("case " + t + " of {" + rules.foldRight("")({ case (r1, r2) => r1 + " | " + r2 }) + "}")

//case class Fold(mu : String, t : Type, e : Expr) extends Expr("fold " + e)
//case class Recurse(mu : String, t1 : Type, x : String, t2 : Type, e1 : Expr, e2 : Expr) extends Expr("rec " + x + "." + e1 + " over??? " + e2)