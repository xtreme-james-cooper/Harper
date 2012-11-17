package model

sealed abstract class Value(name : String, val toExpr : Expr) {
  def numVal : Option[Int] = None
  override def toString : String = name
}

case object ZVal extends Value("0", Z) {
  override def numVal = Some(0)
}
case class SVal(e : Value) extends Value(e.numVal match {
  case None    => "S(" + e + ")"
  case Some(n) => (n + 1).toString
}, S(e.toExpr)) {
  override def numVal = for (n <- e.numVal) yield n + 1
}
case class LamVal(v : String, e : Expr, closure : Map[String, Value]) extends Value("\\" + v + " . " + e, Lam(v, UnitTy, e)) //A thunk; e is unevaluated
case object TrivVal extends Value("()", Triv)
case class PairVal(e1 : Value, e2 : Value) extends Value("(" + e1 + ", " + e2 + ")", PairEx(e1.toExpr, e2.toExpr))
case class InLVal(i : Value) extends Value("inl " + i, InL(i.toExpr, UnitTy))
case class InRVal(i : Value) extends Value("inr " + i, InR(i.toExpr, UnitTy))
