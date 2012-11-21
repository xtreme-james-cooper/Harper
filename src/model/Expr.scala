package model

sealed abstract class Expr(name : String) {
  override def toString : String = name
}

case class Var(v : String) extends Expr(v)
case object Z extends Expr("Z")
case class S(e : Expr) extends Expr("S(" + e + ")")
case class Lam(v : String, t : Type, e : Expr) extends Expr("\\" + v + " . " + e)
case class App(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + " " + e2 + ")")
case class Fix(v : String, e : Expr) extends Expr("fix " + v + " in " + e)
case object Triv extends Expr("()")
case class PairEx(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + ", " + e2 + ")")
case class InL(i : Expr) extends Expr("inl " + i)
case class InR(i : Expr) extends Expr("inr " + i)
case class Match(t : Expr, rules : List[Rule]) extends Expr("case " + t + " of {" + rules.foldRight("")({ case (r1, r2) => r1 + " | " + r2 }) + "}")
case class Fold(mu : String, t : Type, e : Expr) extends Expr("fold " + e)
case class Unfold(e : Expr) extends Expr("unfold " + e)
case class TypeLam(t : String, e : Expr) extends Expr("/\\" + t + " . " + e)
case class TypeApp(e : Expr, t : Type) extends Expr("[" + e + " " + t + "]")
case class ThrowEx(s : String) extends Expr("throw " + s) //TODO make exceptions more complicated than just strings
case class TryCatch(e1 : Expr, e2 : Expr) extends Expr("try " + e1 + " catch " + e2)
case class CommandExp(c : Command) extends Expr("command " + c)