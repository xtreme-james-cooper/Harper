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

case class SetV(v : Value) extends PatternOpcode("??? setv " + v) {
  override def execute : Unit = {
    PatternCPU.v = v
    PatternCPU.valTag = v match {
      case ZVal | TrivVal | PairVal(_, _) | InLVal(_) | FoldVal(_) => 0
      case SVal(_) | InRVal(_) => 1
      case _ => throw new Exception("not possible in pattern matching!" + v)
    }
    PatternCPU.loadStack = v match {
      case PairVal(v2, v3) => v2 :: v3 :: PatternCPU.loadStack
      case InLVal(v2)      => v2 :: PatternCPU.loadStack
      case FoldVal(v2)     => v2 :: PatternCPU.loadStack
      case SVal(v2)        => v2 :: PatternCPU.loadStack
      case InRVal(v2)      => v2 :: PatternCPU.loadStack
      case _               => PatternCPU.loadStack
    }
  }
}

case object ResetV extends PatternOpcode("??? resetv") {
  override def execute : Unit = PatternCPU.loadStack = List(PatternCPU.backup)
}

case object NoRegPop extends PatternOpcode("??? noregpop") {
  override def execute : Unit = {
    val v = PatternCPU.loadStack.head
    PatternCPU.loadStack = PatternCPU.loadStack.tail
    PatternCPU.v = v
  }
}

case object PopLoadStack extends PatternOpcode("??? poploadstack") {
  override def execute : Unit = {
    val v = PatternCPU.loadStack.head
    PatternCPU.loadStack = PatternCPU.loadStack.tail
    PatternCPU.v = v
    PatternCPU.valTag = v match {
      case ZVal | TrivVal | PairVal(_, _) | InLVal(_) | FoldVal(_) => 0
      case SVal(_) | InRVal(_) => 1
      case _ => throw new Exception("not possible in pattern matching!" + v)
    }
    PatternCPU.loadStack = v match {
      case PairVal(v2, v3) => v2 :: v3 :: PatternCPU.loadStack
      case InLVal(v2)      => v2 :: PatternCPU.loadStack
      case FoldVal(v2)     => v2 :: PatternCPU.loadStack
      case SVal(v2)        => v2 :: PatternCPU.loadStack
      case InRVal(v2)      => v2 :: PatternCPU.loadStack
      case _               => PatternCPU.loadStack
    }
  }
}

case object ClearRetStack extends PatternOpcode("??? clearretstack") {
  override def execute : Unit = PatternCPU.matchRetvalStack = Nil
}

case object PushRetStack extends PatternOpcode("??? pushretstack") {
  override def execute : Unit = PatternCPU.matchRetvalStack = PatternCPU.matchRetval :: PatternCPU.matchRetvalStack
}

case object PopRetStack extends PatternOpcode("??? popretstack") {
  override def execute : Unit = {
    val v = PatternCPU.matchRetvalStack.head
    PatternCPU.matchRetvalStack = PatternCPU.matchRetvalStack.tail
    PatternCPU.matchRetval = PatternCPU.matchRetval ++ v
  }
}

case class SetRetval(x : Expr) extends PatternOpcode("??? setretval " + x) {
  override def execute : Unit = PatternCPU.retval = x
}

case class SetMatchRetval(x : Map[String, Value]) extends PatternOpcode("??? setmatchretval " + x) {
  override def execute : Unit = PatternCPU.matchRetval = x
}

case class AddMatchRetval(x : String) extends PatternOpcode("??? addmatchretval " + x) {
  override def execute : Unit = PatternCPU.matchRetval = Map(x -> PatternCPU.v)
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
  