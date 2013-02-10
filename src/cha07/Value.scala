package cha07

sealed abstract class Value(name : String, val toExpr : Expr) {
  override def toString : String = name
}

case class StrVal(s : String) extends Value("\"" + s + "\"", Str(s))
case class NumVal(n : Int) extends Value(n.toString, Num(n))
