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
//A thunk; e is unevaluated
case class LamVal(v : String, e : Expr, var closure : Map[String, Value]) extends Value("\\" + v + " . " + e, Lam(v, UnitTy, e))
//Includes a reference to itself in the closure; this is the one place (so far) that we *need* vars
object RecursiveLamVal {
  def apply(n : String, v : String, e : Expr, closure : Map[String, Value]) : LamVal = {
    val lam = LamVal(v, e, closure)
    lam.closure = lam.closure + (n -> lam)
    lam
  }
}
case object TrivVal extends Value("()", Triv)
case class PairVal(e1 : Value, e2 : Value) extends Value("(" + e1 + ", " + e2 + ")", PairEx(e1.toExpr, e2.toExpr))
case class InLVal(i : Value) extends Value("inl " + i, InL(i.toExpr))
case class InRVal(i : Value) extends Value("inr " + i, InR(i.toExpr))
case class FoldVal(v : Value) extends Value("fold " + v, Fold("", UnitTy, v.toExpr)) 
case class Action(c : Command, closure : Map[String, Value]) extends Value("command " + c, CommandExp(c))

//Distinguished exception value
case class ExceptionValue(s : String) extends Value("!" + s + "!", ThrowEx(s))

