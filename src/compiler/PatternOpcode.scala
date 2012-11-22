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

case class HeapPush(h : HeapValue) extends PatternOpcode("??? aloc " + h) {
  override def execute : Unit = {
    valHeap(register(R_VAL_HP)) = h
    register(R_VAL_HP) = register(R_VAL_HP) + 1
  }
}

case class ValPush(v : HeapValue) extends PatternOpcode("??? pshv " + v) {
  override def execute : Unit = {
    valStack(register(R_VAL_SP)) = valHeap(0) //TODO not correct atm
    register(R_VAL_SP) = register(R_VAL_SP) + 1
  }
}

case class ValPushA(x : HeapValue) extends PatternOpcode("??? pshv " + v) {
  override def execute : Unit = {
    valStack(register(R_VAL_SP)) = v.a //TODO not correct atm
    register(R_VAL_SP) = register(R_VAL_SP) + 1
  }
}

case class ValPushB(x : HeapValue) extends PatternOpcode("??? pshv " + v) {
  override def execute : Unit = {
    valStack(register(R_VAL_SP)) = v.b //TODO not correct atm
    register(R_VAL_SP) = register(R_VAL_SP) + 1
  }
}

case object ValPop extends PatternOpcode("??? popv") {
  override def execute : Unit = {
    register(R_VAL_SP) = register(R_VAL_SP) - 1
    v = valStack(register(R_VAL_SP))
    register(R_TAG) = v.tag
  }
}

case class PushVRetStack(x : String) extends PatternOpcode("??? pshe " + x + " -> v") {
  override def execute : Unit = {
    bindStack(register(R_BIND_SP)) = (x -> v)
    register(R_BIND_SP) = register(R_BIND_SP) + 1
  }
}

case class SetRetval(x : Expr) extends PatternOpcode("??? sete") {
  override def execute : Unit = retval = x
}
  