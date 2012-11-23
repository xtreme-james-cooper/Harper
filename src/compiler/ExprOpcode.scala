package compiler

import ExprCPU._
import model.{ Value, SVal, Expr, ExceptionValue }
import model.InRVal
import model.InLVal
import model.PairVal

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

case class RunExpr(e : Expr) extends ExprOpcode("???? runex " + e) {
  override def execute : Unit = retval = ExprCompiler.doEval(e, env) :: retval
}

case class ReturnOp(v : Value) extends ExprOpcode("???? retval " + v) {
  override def execute : Unit = retval = v :: retval
}

case class JIfExn(l : String) extends ExprOpcode("???? jifx :" + l) {
  override def execute : Unit =
    if (retval.head.isInstanceOf[ExceptionValue]) {
      PC = 0
      while (prog(PC) != ExprLabel(l)) {
        PC = PC + 1
      }
    }
}

case object PushS extends ExprOpcode("???? pshS") {
  override def execute : Unit = retval = SVal(retval.head) :: retval.tail
}

case object PushInR extends ExprOpcode("???? pshinR") {
  override def execute : Unit = retval = InRVal(retval.head) :: retval.tail
}

case object PushInL extends ExprOpcode("???? pshinL") {
  override def execute : Unit = retval = InLVal(retval.head) :: retval.tail
}

case object PushPair extends ExprOpcode("???? pshpair") {
  override def execute : Unit = retval = PairVal(retval.tail.head, retval.head) :: retval.tail.tail
}


