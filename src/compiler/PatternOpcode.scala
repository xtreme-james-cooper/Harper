package compiler

import model.Value
import model.Rule
import model.Pattern
import model.Expr
import model.ZVal

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

case class Label(l : String) extends PatternOpcode("   " + l + ":") {
  override def execute : Unit = throw new Exception("Executing label " + l)
}

case class SetV(v : Value) extends PatternOpcode("??? setv " + v) {
  override def execute : Unit = PatternCPU.v = v
}

case class SetRetval(x : Expr) extends PatternOpcode("??? setretval" + x) {
  override def execute : Unit = PatternCPU.retval = x
}

case class SetIsEv(x : Boolean) extends PatternOpcode("??? setisEv" + x) {
  override def execute : Unit = PatternCPU.isEvaluated = x
}

case class SetMatchRetval(x : Map[String, Value]) extends PatternOpcode("??? setmatchretval" + x) {
  override def execute : Unit = PatternCPU.matchRetval = x
}

case class AddMatchRetval(x : String) extends PatternOpcode("??? addmatchretval" + x) {
  override def execute : Unit = PatternCPU.matchRetval = PatternCPU.matchRetval + (x -> PatternCPU.v)
}

case class RunMatch(p : Pattern) extends PatternOpcode("??? runmatch" + p) {
  override def execute : Unit = {
    val (isEv, body) = PatternCompiler.runMatch(p, null)
    PatternCPU.matchRetval = body
    PatternCPU.isEvaluated = isEv
  }
}

case class Jump(l : String) extends PatternOpcode("jump " + l) { //TODO do search better
  override def execute : Unit = {
    PatternCPU.PC = 0
    while (PatternCPU.prog(PatternCPU.PC) != Label(l)) {
      PatternCPU.PC = PatternCPU.PC + 1
    }
  }
}

case class JIfIsEvB(l : String) extends PatternOpcode("??? jifisevb " + l) { //TODO do search better
  override def execute : Unit =
    if (PatternCPU.isEvaluated) {
      PatternCPU.PC = 0
      while (PatternCPU.prog(PatternCPU.PC) != Label(l)) {
        PatternCPU.PC = PatternCPU.PC + 1
      }
    }
}

case class JIfNZ(l : String) extends PatternOpcode("??? jifnz " + l) { //TODO do search better
  override def execute : Unit =
    if (PatternCPU.v != ZVal) {
      PatternCPU.PC = 0
      while (PatternCPU.prog(PatternCPU.PC) != Label(l)) {
        PatternCPU.PC = PatternCPU.PC + 1
      }
    }
}
  