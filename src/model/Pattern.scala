package model

sealed abstract class Pattern(name : String, val freeVars : List[String]) {
  override def toString : String = name
}

case object WildPat extends Pattern("_", Nil)
case class VarPat(x : String) extends Pattern(x, List(x))
case object TrivPat extends Pattern("()", Nil)
case object ZPat extends Pattern("Z", Nil)
case class SPat(e : Pattern) extends Pattern("S(" + e + ")", e.freeVars)
case class PairPat(e1 : Pattern, e2 : Pattern) extends Pattern("(" + e1 + ", " + e2 + ")", e1.freeVars ++ e2.freeVars)
case class InLPat(i : Pattern) extends Pattern("inl " + i, i.freeVars)
case class InRPat(i : Pattern) extends Pattern("inr " + i, i.freeVars)