package model

sealed abstract class Command(name : String) {
  override def toString : String = name
}

case class Ret(e : Expr) extends Command("return " + e)
case class Bind(x : String, e : Expr, m : Command) extends Command("bind " + x + " <- " + e + "; " + m)
case class Decl(x : String, e : Expr, m : Command) extends Command("decl " + x + " := " + e + " in " + m)
case class Get(x : String) extends Command("!" + x)
case class SetCmd(x : String, e : Expr, m : Command) extends Command(x + " := " + e + ";" + m)