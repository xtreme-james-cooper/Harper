package compiler

import ExprCPU._
import model.Expr

sealed abstract class ExprOpcode(name : String) {
  override def toString : String = name
  def execute : Unit
}

case object ExprExit extends ExprOpcode("exit") {
  override def execute : Unit = throw new Exception("Executing exit opcode")
}

case class ExprThrw(s : String) extends ExprOpcode("thrw \"" + s + "\"") {
  override def execute : Unit = throw new Exception(s)
}

case class ExprLabel(l : String) extends ExprOpcode("   :" + l + "") {
  override def execute : Unit = ()
}




/*
 * Bogus
 */

case class RunExpr(e : Expr) extends ExprOpcode("???? rune " + e) {
  override def execute : Unit = retval = ExprCompiler.doEval(e, env)
}