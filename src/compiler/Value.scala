package compiler

import model.ThrowEx
import model.Expr
import model.PairEx
import model.InR
import model.Lam
import model.CommandExp
import model.InL
import model.Triv
import model.Z
import model.S
import model.Command
import model.Fold
import model.UnitTy

sealed abstract class Value(name : String) {
  def numVal : Option[Int] = None
  override def toString : String = name
}

case object ZVal extends Value("0") {
  override def numVal = Some(0)
}
case class SVal(e : Value) extends Value(e.numVal match {
  case None    => "S(" + e + ")"
  case Some(n) => (n + 1).toString
}) {
  override def numVal = for (n <- e.numVal) yield n + 1
}
//A thunk; e is unevaluated
case class LamVal(v : String, codePointer : String, var closure : Map[String, Value]) extends Value("call " + codePointer)
//Includes a reference to itself in the closure; this is the one place (so far) that we *need* vars
object RecursiveLamVal {
  def apply(name : String, x : String, closure : Map[String, Value]) : LamVal = {
    val lam = LamVal(x, name, closure)
    lam.closure = lam.closure + (name -> lam)
    lam
  }
}
case object TrivVal extends Value("()")
case class PairVal(e1 : Value, e2 : Value) extends Value("(" + e1 + ", " + e2 + ")")
case class InLVal(i : Value) extends Value("inl " + i)
case class InRVal(i : Value) extends Value("inr " + i)
case class FoldVal(v : Value) extends Value("fold " + v) 
case class Action(c : Command, closure : Map[String, Value]) extends Value("command " + c)

//Distinguished exception value
case class ExceptionValue(s : String) extends Value("!" + s + "!")

