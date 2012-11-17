package model

sealed abstract class Expr(name : String) {
  def replace(v : String, e : Expr) : Expr
  def replace(binds : Map[String, Expr]) : Expr = binds.foldLeft(this)({ case (e, (v, b)) => e.replace(v, b) })
  def numVal : Option[Int] = None
  override def toString : String = name
}

case class Var(v : String) extends Expr(v) {
  override def replace(vbl : String, e : Expr) : Expr = if (v == vbl) e else this
}

case object Z extends Expr("0") {
  override def numVal = Some(0)
  override def replace(v : String, e : Expr) : Expr = this
}

case class S(e : Expr) extends Expr(e.numVal match {
  case None    => "S(" + e + ")"
  case Some(n) => (n + 1).toString
}) {
  override def numVal = for (n <- e.numVal) yield n + 1
  override def replace(v : String, e1 : Expr) : Expr = S(e.replace(v, e1))
}

case class Lam(v : String, t : Type, e : Expr) extends Expr("\\" + v + " . " + e) {
  override def replace(vbl : String, e1 : Expr) : Expr = Lam(v, t, if (v == vbl) e else e.replace(vbl, e1))
}

case class App(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + " " + e2 + ")") {
  override def replace(v : String, e : Expr) : Expr = App(e1.replace(v, e), e2.replace(v, e))
}

case class Fix(v : String, t : Type, e : Expr) extends Expr("fix " + v + " in " + e) {
  override def replace(vbl : String, e1 : Expr) : Expr = Fix(v, t, if (v == vbl) e else e.replace(vbl, e1))
}

case object Triv extends Expr("()") {
  override def replace(vbl : String, e1 : Expr) : Expr = this
}

case class PairEx(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + ", " + e2 + ")") {
  override def replace(v : String, e : Expr) : Expr = PairEx(e1.replace(v, e), e2.replace(v, e))
}

case class InL(i : Expr, t : Type) extends Expr("inl " + i) {
  override def replace(v : String, e : Expr) : Expr = InL(i.replace(v, e), t)
}

case class InR(i : Expr, t : Type) extends Expr("inr " + i) {
  override def replace(v : String, e : Expr) : Expr = InR(i.replace(v, e), t)
}

case class Match(t : Expr, rules : List[Rule]) extends Expr("case " + t + " of {" + rules.foldRight("")({ case (r1, r2) => r1 + " | " + r2 }) + "}") {
  override def replace(v : String, e : Expr) : Expr = Match(t.replace(v, e), rules.map(_ replace (v, e)))
}