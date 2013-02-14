package cha14

sealed abstract class Value(name : String, val toExpr : Expr, val toInt : Int) {
  def this(name : String, toExpr : Expr) = this(name, toExpr, Integer.MIN_VALUE)
  override def toString : String = name
}

case object ZVal extends Value("0", Z, 0)
case class SVal(n : Value) extends Value((n.toInt + 1).toString, S(n.toExpr), n.toInt + 1)
case class LamVal(x : String, e : Expr) extends Value("\\" + x + " . " + e, Lam(UnitTy, x, e))
case class PairVal(v1 : Value, v2 : Value) extends Value("(" + v1 + ", " + v2 + ")", Pair(v1.toExpr, v2.toExpr))
case object TrivVal extends Value("()", Triv)
case class InLVal(v : Value) extends Value("inl (" + v + ")", InL(UnitTy, v.toExpr))
case class InRVal(v : Value) extends Value("inr (" + v + ")", InR(UnitTy, v.toExpr))