package model

case class Rule(p : Pattern, b : Expr) {
  override def toString : String = p + " -> " + b
  def replace(v : String, e : Expr) : Rule = new Rule(p, if (p.freeVars.contains(v)) b else b.replace(v, e))
}