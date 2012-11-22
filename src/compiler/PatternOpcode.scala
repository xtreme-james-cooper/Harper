package compiler

import model.Value
import model.Rule
import model.Pattern

sealed abstract class PatternOpcode(name : String) {
  override def toString : String = name
  def execute : Unit
}

case object Exit extends PatternOpcode("exit") {
  override def execute : Unit = throw new Exception("Executing exit opcode")
}

case class Thrw(s : String) extends PatternOpcode("thrw \"" + s + "\"") {
  override def execute : Unit = throw new Exception(s)
}

case class SetV(v : Value) extends PatternOpcode("??? setv " + v) {
  override def execute : Unit = PatternCPU.v = v
}

case class RunRules(rs : List[Rule]) extends PatternOpcode("??? runrules" + rs) {
  override def execute : Unit = PatternCPU.retval = PatternCompiler.runRules(rs)
}

case class RunMatch(p : Pattern, retval : Map[String, Value]) extends PatternOpcode("??? runmatch" + p + " " + retval) {
  override def execute : Unit = PatternCPU.matchRetval = PatternCompiler.runMatch(p, retval)
}