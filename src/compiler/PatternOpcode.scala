package compiler

import model.{ZVal, Value, TrivVal, SVal, PairVal, InRVal, InLVal, FoldVal, Expr}
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
  override def execute : Unit = throw new Exception("Executing label " + l)
}

case object ResetV extends PatternOpcode("rstv") {
  override def execute : Unit = {
    valStack(0) = backup
    register(VAL_SP_REGISTER) = 1
  }
}

case object ValPop extends PatternOpcode("popv") {
  override def execute : Unit = {
    register(VAL_SP_REGISTER) = register(VAL_SP_REGISTER) - 1
    v = valStack(register(VAL_SP_REGISTER))
    register(TAG_REGISTER) = v match {
      case ZVal          => 0
      case SVal(_)       => 1
      case InLVal(_)     => 2
      case InRVal(_)     => 3
      case TrivVal       => 4
      case PairVal(_, _) => 5
      case FoldVal(_)    => 6
      case _             => throw new Exception("not possible in pattern matching!" + v)
    }
  }
}

case object VIntoReg extends PatternOpcode("??? pushloadstack") {
  override def execute : Unit = {
    v match {
      case PairVal(v2, v3) => {
        valStack(register(VAL_SP_REGISTER)) = v3
        valStack(register(VAL_SP_REGISTER) + 1) = v2
        register(VAL_SP_REGISTER) = register(VAL_SP_REGISTER) + 2
      }
      case InLVal(v2) => {
        valStack(register(VAL_SP_REGISTER)) = v2
        register(VAL_SP_REGISTER) = register(VAL_SP_REGISTER) + 1
      }
      case FoldVal(v2) => {
        valStack(register(VAL_SP_REGISTER)) = v2
        register(VAL_SP_REGISTER) = register(VAL_SP_REGISTER) + 1
      }
      case SVal(v2) => {
        valStack(register(VAL_SP_REGISTER)) = v2
        register(VAL_SP_REGISTER) = register(VAL_SP_REGISTER) + 1
      }
      case InRVal(v2) => {
        valStack(register(VAL_SP_REGISTER)) = v2
        register(VAL_SP_REGISTER) = register(VAL_SP_REGISTER) + 1
      }
      case _ => ()
    }
  }
}

case object ClearRetStack extends PatternOpcode("rstr") {
  override def execute : Unit = register(BIND_SP_REGISTER) = 0
}

case object PushRetStack extends PatternOpcode("pshr") {
  override def execute : Unit = {
    bindStack(register(BIND_SP_REGISTER)) = matchRetval
    register(BIND_SP_REGISTER) = register(BIND_SP_REGISTER) + 1
  }
}

case object PopRetStack extends PatternOpcode("popr") {
  override def execute : Unit = {
    register(BIND_SP_REGISTER) = register(BIND_SP_REGISTER) - 1
    matchRetval = matchRetval ++ bindStack(register(BIND_SP_REGISTER))
  }
}

case class SetRetval(x : Expr) extends PatternOpcode("setr") {
  override def execute : Unit = retval = x
}

case class SetMatchRetval(x : List[(String, Value)]) extends PatternOpcode("setm") {
  override def execute : Unit = matchRetval = x
}

case class AddMatchRetval(x : String) extends PatternOpcode("??? addmatchretval " + x) {
  override def execute : Unit = matchRetval = List(x -> v)
}

case class Jump(l : String) extends PatternOpcode("jump :" + l) { //TODO do search better
  override def execute : Unit = {
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
  