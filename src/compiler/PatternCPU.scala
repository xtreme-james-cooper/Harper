package compiler

import model.Expr
import model.Value

object PatternCPU {

  var PC : Int = 0
  
  var v : Value = null
  
  var retval : (Expr, Map[String, Value]) = null
  
  var matchRetval : (Boolean, Map[String, Value]) = null
  
  def run(v1 : Value, prog : Array[PatternOpcode]) : (Expr, Map[String, Value]) = {
    PC = 0
    v = v1
    while (prog(PC) != Exit) {
      prog(PC).execute
      PC = PC + 1
    }
    retval
  }
  
  
}