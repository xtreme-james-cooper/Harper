package compiler

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