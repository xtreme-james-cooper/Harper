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

  var v : Value = null

  var retval : Expr = null

  var isEvaluated : Boolean = false

  var matchRetval : Map[String, Value] = null

  def run(v1 : Value, pr : Array[PatternOpcode]) : (Expr, Map[String, Value]) = {
    PC = 0
    prog = pr
    v = v1
    while (prog(PC) != Exit) {
      prog(PC).execute
      PC = PC + 1
    }
    (retval, matchRetval)
  }

}