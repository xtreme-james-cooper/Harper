package compiler

import CommandCPU._
import model.Command
import model.Expr

sealed abstract class CommandOpcode(name : String) {
  override def toString : String = name
  def execute : Unit
}

case object CmdExit extends CommandOpcode("exit") {
  override def execute : Unit = throw new Exception("Executing exit opcode")
}

case class CmdThrw(s : String) extends CommandOpcode("thrw \"" + s + "\"") {
  override def execute : Unit = throw new Exception(s)
}

case class CmdLabel(l : String) extends CommandOpcode("   :" + l + "") {
  override def execute : Unit = ()
}

case class CmdJump(l : String) extends CommandOpcode("jump :" + l) {
  override def execute : Unit = goto(l)
}


/*
 * Bogus
 */

case class CmdReturn(v : Value) extends CommandOpcode("???? retval " + v) {
  override def execute : Unit = retval = v
}

case class ExprRun(e : Expr) extends CommandOpcode("???? runexpr " + e) {
  override def execute : Unit = retval = ExprCompiler.run(e, env, subdefs)
}

case class PushToMem(x : String) extends CommandOpcode("???? pushtomem " + x) {
  override def execute : Unit = mem = CommandCompiler.updateMemory(x, retval, mem)
}

case class PushToEnv(x : String) extends CommandOpcode("???? pushtomem " + x) {
  override def execute : Unit = env = Map(x -> retval) :: env
}

case class DerefAssgnable(x : String) extends CommandOpcode("???? derefassg " + x) {
  override def execute : Unit = retval = CommandCompiler.getBinding(mem, x)
}

case object PerformAction extends CommandOpcode("???? perform") {
  override def execute : Unit = retval = {
    CommandCompiler.executeCommand(retval.asInstanceOf[Action].c, retval.asInstanceOf[Action].closure :: env, mem, subdefs)
  }
}