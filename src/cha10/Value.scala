package cha10

sealed abstract class Value(name : String, val toExpr : Expr, val toInt : Int) {
  override def toString : String = name
}

case object ZVal extends Value("0", Z, 0)
case class SVal(n : Value) extends Value((n.toInt + 1).toString, S(n.toExpr), n.toInt + 1)
case class LamVal(t : Type, x : String, e : Expr) extends Value("\\" + x + ":" + t + " . " + e, Lam(t, x, e), Integer.MIN_VALUE)