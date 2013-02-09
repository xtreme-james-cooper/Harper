package all.model

sealed abstract class Pattern(name : String, val freeVars : Set[String]) {
  override def toString : String = name
}

case object WildPat extends Pattern("_", Set())
case class VarPat(x : String) extends Pattern(x, Set(x))
case object TrivPat extends Pattern("()", Set())
case class PairPat(p1 : Pattern, p2 : Pattern) extends Pattern("(" + p1 + ", " + p2 + ")", p1.freeVars | p2.freeVars)
case class InLPat(p : Pattern) extends Pattern("inL " + p, p.freeVars)
case class InRPat(p : Pattern) extends Pattern("inR " + p, p.freeVars)
case object ZPat extends Pattern("Z", Set())
case class SPat(p : Pattern) extends Pattern("S(" + p + ")", p.freeVars)
