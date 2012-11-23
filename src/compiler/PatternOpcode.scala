package compiler

import model.{ ZVal, Value, TrivVal, SVal, PairVal, InRVal, InLVal, FoldVal, Expr }
import PatternCPU._

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

case class Label(l : String) extends PatternOpcode("   :" + l + "") {
  override def execute : Unit = ()
}

case class SetReg(n : Int, v : Int) extends PatternOpcode("setr r" + n + " #" + v) {
  override def execute : Unit = register(n) = v
}

case class Add1(n : Int) extends PatternOpcode("add1 r" + n) {
  override def execute : Unit = register(n) = register(n) + 1
}

case class Jump(l : String) extends PatternOpcode("jump :" + l) { //TODO do search better
  override def execute : Unit = {
    PC = 0
    while (prog(PC) != Label(l)) {
      PC = PC + 1
    }
  }
}

case class JIfLEq(n : Int, v : Int, l : String) extends PatternOpcode("jile r" + n + " #" + v + " :" + l) { //TODO do search better
  override def execute : Unit =
    if (register(n) <= v) {
      PC = 0
      while (prog(PC) != Label(l)) {
        PC = PC + 1
      }
    }
}

case class JIfNEq(n : Int, v : Int, l : String) extends PatternOpcode("jine r" + n + " #" + v + " :" + l) { //TODO do search better
  override def execute : Unit =
    if (register(n) != v) {
      PC = 0
      while (prog(PC) != Label(l)) {
        PC = PC + 1
      }
    }
}

case class ValPush(x : Int) extends PatternOpcode("pshv r" + x) {
  override def execute : Unit = {
    valStack(register(R_VAL_SP)) = valHeap(register(x))
    register(R_VAL_SP) = register(R_VAL_SP) + 1
  }
}

case class ValPop(x : Int) extends PatternOpcode("popv r" + x) {
  override def execute : Unit = {
    register(R_VAL_SP) = register(R_VAL_SP) - 1
    register(x) = valStack(register(R_VAL_SP))
  }
}

case class PushVRetStack(x : String) extends PatternOpcode("??? pshe " + x + " -> v") {
  override def execute : Unit = {
    bindStack(register(R_BIND_SP)) = (x -> (register(R_TAG), register(R_HEAP_A), register(R_HEAP_B)))
    register(R_BIND_SP) = register(R_BIND_SP) + 1
  }
}

case class SetRetval(x : Expr) extends PatternOpcode("sete " + x) {
  override def execute : Unit = retval = x
}
  