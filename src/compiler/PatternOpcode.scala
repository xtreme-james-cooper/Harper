package compiler

import model.Value
import model.Rule
import model.Pattern
import model.Expr
import model.ZVal
import model.TrivVal
import model.PairVal
import model.InLVal
import model.FoldVal
import model.SVal
import model.InRVal

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

case object ResetV extends PatternOpcode("rstv") {
  override def execute : Unit = {
    PatternCPU.valStack(0) = PatternCPU.backup
    PatternCPU.valSP = 1
  }
}

case object ValPop extends PatternOpcode("popv") {
  override def execute : Unit = {
    PatternCPU.valSP = PatternCPU.valSP - 1
    PatternCPU.v = PatternCPU.valStack(PatternCPU.valSP)
  }
}

case object VIntoReg extends PatternOpcode("??? poploadstack") {
  override def execute : Unit = {
    PatternCPU.valTag = PatternCPU.v match {
      case ZVal          => 0
      case SVal(_)       => 1
      case InLVal(_)     => 2
      case InRVal(_)     => 3
      case TrivVal       => 4
      case PairVal(_, _) => 5
      case FoldVal(_)    => 6
      case _             => throw new Exception("not possible in pattern matching!" + PatternCPU.v)
    }
    PatternCPU.v match {
      case PairVal(v2, v3) => {
        PatternCPU.valStack(PatternCPU.valSP) = v3
        PatternCPU.valStack(PatternCPU.valSP + 1) = v2
        PatternCPU.valSP = PatternCPU.valSP + 2
      }
      case InLVal(v2) => {
        PatternCPU.valStack(PatternCPU.valSP) = v2
        PatternCPU.valSP = PatternCPU.valSP + 1
      }
      case FoldVal(v2) => {
        PatternCPU.valStack(PatternCPU.valSP) = v2
        PatternCPU.valSP = PatternCPU.valSP + 1
      }
      case SVal(v2) => {
        PatternCPU.valStack(PatternCPU.valSP) = v2
        PatternCPU.valSP = PatternCPU.valSP + 1
      }
      case InRVal(v2) => {
        PatternCPU.valStack(PatternCPU.valSP) = v2
        PatternCPU.valSP = PatternCPU.valSP + 1
      }
      case _ => ()
    }
  }
}

case object ClearRetStack extends PatternOpcode("??? clearretstack") {
  override def execute : Unit = PatternCPU.bindSP = 0
}

case object PushRetStack extends PatternOpcode("??? pushretstack") {
  override def execute : Unit = {
    PatternCPU.bindStack(PatternCPU.bindSP) = PatternCPU.matchRetval
    PatternCPU.bindSP = PatternCPU.bindSP + 1
  }
}

case object PopRetStack extends PatternOpcode("??? popretstack") {
  override def execute : Unit = {
    PatternCPU.bindSP = PatternCPU.bindSP - 1
    PatternCPU.matchRetval = PatternCPU.matchRetval ++ PatternCPU.bindStack(PatternCPU.bindSP)
  }
}

case class SetRetval(x : Expr) extends PatternOpcode("??? setretval " + x) {
  override def execute : Unit = PatternCPU.retval = x
}

case class SetMatchRetval(x : Map[String, Value]) extends PatternOpcode("??? setmatchretval " + x) {
  override def execute : Unit = PatternCPU.matchRetval = x
}

case class AddMatchRetval(x : String) extends PatternOpcode("??? addmatchretval " + x) {
  override def execute : Unit = {
    //    val v : Value = PatternCPU.valTag match {
    //      case 0 => ZVal
    //      case 1 => SVal(PatternCPU.loadStack.head)
    //      case 2 => InLVal(PatternCPU.loadStack.head)
    //      case 3 => InRVal(PatternCPU.loadStack.head)
    //      case 4 => TrivVal
    //      case 5 => PairVal(PatternCPU.loadStack.head, PatternCPU.loadStack.tail.head)
    //      case 6 => FoldVal(PatternCPU.loadStack.head)
    //    }
    //    if (v != PatternCPU.v) throw new Exception("huh?")
    PatternCPU.matchRetval = Map(x -> PatternCPU.v)
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

case class JIfValtagNEq(v : Int, l : String) extends PatternOpcode("??? jifvaltagneq " + v + " " + l) { //TODO do search better
  override def execute : Unit =
    if (PatternCPU.valTag != v) {
      PatternCPU.PC = 0
      while (PatternCPU.prog(PatternCPU.PC) != Label(l)) {
        PatternCPU.PC = PatternCPU.PC + 1
      }
    }
}
  