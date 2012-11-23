package compiler

import ExprCPU._
import model.{Rule, Expr, Command}

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
  override def execute : Unit = {
    PC = 0
    while (prog(PC) != ExprLabel(l)) {
      PC = PC + 1
    }
  }
}

/*
 * Bogus
 */

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

case class JIfNExn(l : String) extends ExprOpcode("???? jifnx :" + l) {
  override def execute : Unit =
    if (!retval.head.isInstanceOf[ExceptionValue]) {
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

case object PushFold extends ExprOpcode("???? pshfold") {
  override def execute : Unit = retval = FoldVal(retval.head) :: retval.tail
}

case class PushLam(x : String, e : Expr) extends ExprOpcode("???? pshlam " + x + " " + e) {
  override def execute : Unit = retval = LamVal(x, e, envTemp) :: retval
}

case class PushCommand(c : Command) extends ExprOpcode("???? pshcom " + c) {
  override def execute : Unit = retval = Action(c, envTemp) :: retval
}

case object PopFold extends ExprOpcode("???? popfold") {
  override def execute : Unit = retval = retval.head.asInstanceOf[FoldVal].v :: retval.tail
}

case class RunPat(rs : List[Rule]) extends ExprOpcode("???? runPat " + rs) {
  override def execute : Unit = patReturn = PatternCompiler.run(retval.head, rs)
}

case object RunExprFromPat extends ExprOpcode("???? runexfrompat ") {
  override def execute : Unit = retval = ExprCompiler.doEval(patReturn._1, env) :: retval
}

case object PushEnvFromPat extends ExprOpcode("???? pshenvfrompat") {
  override def execute : Unit = env = patReturn._2 :: env
}

case object PopEnv extends ExprOpcode("???? popenv") {
  override def execute : Unit = env = env.tail
}

case object RunLambda extends ExprOpcode("???? runlam") {
  override def execute : Unit = {
	val v = retval.head
	retval = retval.tail
    val l = retval.head.asInstanceOf[LamVal]
	retval = retval.tail
    env = (l.closure + (l.v -> v)) :: env
    retval = ExprCompiler.doEval(l.e, env) :: retval
  }
}

case object FlattenEnv extends ExprOpcode("???? flattenv") {
  override def execute : Unit = envTemp = ExprCompiler.flatten(env)
}

case class PushRecursiveLamEnv(v : String, x : String, e : Expr) extends ExprOpcode("???? pushrecursivelamenv") {
  override def execute : Unit = envTemp = ExprCompiler.flatten(Map(v -> RecursiveLamVal(v, x, e, ExprCompiler.flatten(env))) :: env)
}

case class DerefVar(x : String) extends ExprOpcode("???? derefvar " + x) {
  override def execute : Unit = retval = ExprCompiler.getBinding(env, x) :: retval
}
