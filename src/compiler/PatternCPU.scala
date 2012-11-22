package compiler

import model.Expr
import model.Value
import model.TrivVal
import model.InLVal
import model.ZVal
import model.InRVal
import model.PairVal
import model.SVal
import model.FoldVal

object PatternCPU {

  var PC : Int = 0
  var prog : Array[PatternOpcode] = null

  var valTag : Int = 0
  var loadStack : List[Value] = Nil

  var v : Value = null

  var retval : Expr = null

  var isEvaluated : Int = 0

  var matchRetval : Map[String, Value] = null

  def run(v1 : Value, pr : Array[PatternOpcode]) : (Expr, Map[String, Value]) = {
    PC = 0
    prog = pr
    loadStack = Nil
    
//    pr.foreach(println)
    
    valueToRegisters(v1)
    while (prog(PC) != Exit) {
      prog(PC).execute
      PC = PC + 1
    }
    (retval, matchRetval)
  }

  def valueToRegisters(v1 : Value) : Unit = {
    v = v1
    valTag = v1 match {
      case ZVal | TrivVal | PairVal(_, _) | InLVal(_) | FoldVal(_) => 0
      case SVal(_) | InRVal(_) => 1
      case _ => throw new Exception("not possible in pattern matching!" + v1)
    }
    loadStack = v1 match {
      case PairVal(v2, v3) => v2 :: v3 :: loadStack
      case InLVal(v2) => v2 :: loadStack
      case FoldVal(v2) => v2 :: loadStack
      case SVal(v2) => v2 :: loadStack
      case InRVal(v2) => v2 :: loadStack
      case _ => loadStack
    }
  }

}