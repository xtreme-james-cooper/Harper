package compiler

import ExprCPU._
import model.{ Rule, Expr, Command }
import model.Pattern

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

case class ExprJump(l : String) extends ExprOpcode("???? jump :" + l) {
  override def execute : Unit = goto(l)
}

/*
 * Bogus
 */

case class ReturnOp(v : Value) extends ExprOpcode("???? retval " + v) {
  override def execute : Unit = retval = v :: retval
}

case class JIfExn(l : String) extends ExprOpcode("???? jifx :" + l) {
  override def execute : Unit = if (retval.head.isInstanceOf[ExceptionValue]) goto(l)
}

case class JIfNExn(l : String) extends ExprOpcode("???? jifnx :" + l) {
  override def execute : Unit = if (!retval.head.isInstanceOf[ExceptionValue]) goto(l)
}

case object JumpReturn extends ExprOpcode("???? jumpreturn") {
  override def execute : Unit = {
    val l = returnStack.head
    returnStack = returnStack.tail
    goto(l)
  }
}

case class PushReturn(s : String) extends ExprOpcode("???? pushreturn " + s) {
  override def execute : Unit = returnStack = s :: returnStack
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

case object PushFold extends ExprOpcode("???? pshfold") {
  override def execute : Unit = retval = FoldVal(retval.head) :: retval.tail
}

case class PushLam(x : String, codePointer : String) extends ExprOpcode("???? pshlam " + x + " " + codePointer) {
  override def execute : Unit = retval = LamVal(x, codePointer, envTemp) :: retval
}

case class PushCommand(c : Command) extends ExprOpcode("???? pshcom " + c) {
  override def execute : Unit = retval = Action(c, envTemp) :: retval
}

case object PopFold extends ExprOpcode("???? popfold") {
  override def execute : Unit = retval = retval.head.asInstanceOf[FoldVal].v :: retval.tail
}

case class RunPat(rs : List[(Pattern, String)]) extends ExprOpcode("???? runPat " + rs) {
  override def execute : Unit = {
    patReturn = PatternCompiler.run(retval.head, rs)
    env = patReturn._2 :: env
    retval = retval.tail
  }
}

case object JumpPatBody extends ExprOpcode("???? jmppatbdy") {
  override def execute : Unit = goto(patReturn._1)
}

case object PopEnv extends ExprOpcode("???? popenv") {
  override def execute : Unit = env = env.tail
}

case object RunLambda extends ExprOpcode("???? runlam") {
  override def execute : Unit = {
    val l = retval.head.asInstanceOf[LamVal]
    retval = retval.tail
    val v = retval.head
    retval = retval.tail
    env = (l.closure + (l.v -> v)) :: env
    
    goto(l.codePointer)
  }
}

case object FlattenEnv extends ExprOpcode("???? flattenv") {
  override def execute : Unit = envTemp = ExprCompiler.flatten(env)
}

case class DerefVar(x : String) extends ExprOpcode("???? derefvar " + x) {
  override def execute : Unit = retval = ExprCompiler.getBinding(env, x) :: retval
}
