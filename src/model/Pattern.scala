package model

sealed abstract class Pattern(name : String) {
  override def toString : String = name
  def freeVars : List[String]
}

case object WildPat extends Pattern("_") {
  override def freeVars = Nil
}

case class VarPat(x : String) extends Pattern(x) {
  override def freeVars = List(x)
}

case object TrivPat extends Pattern("()") {
  override def freeVars = Nil
}

case object ZPat extends Pattern("Z") {
  override def freeVars = Nil
}

case class SPat(e : Pattern) extends Pattern("S(" + e + ")") {
  override def freeVars = e.freeVars
}

case class PairPat(e1 : Pattern, e2 : Pattern) extends Pattern("(" + e1 + ", " + e2 + ")") {
  override def freeVars = e1.freeVars ++ e2.freeVars
}

case class InLPat(i : Pattern) extends Pattern("inl " + i) {
  override def freeVars = i.freeVars
}

case class InRPat(i : Pattern) extends Pattern("inr " + i) {
  override def freeVars = i.freeVars
}