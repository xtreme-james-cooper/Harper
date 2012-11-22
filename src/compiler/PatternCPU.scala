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
  var prog : List[PatternOpcode] = null

  val register : Array[Int] = Array.ofDim(32)
  val TAG_REGISTER = 0
  val VAL_SP_REGISTER = 1
  val BIND_SP_REGISTER = 2
  
  val valStack : Array[Value] = Array.ofDim(1000) //TODO large enough?
  val bindStack : Array[List[(String, Value)]] = Array.ofDim(1000) //TODO large enough?
  
  var backup : Value = null
  
  var v : Value = null

  var retval : Expr = null
  
  def run(v1 : Value, pr : List[PatternOpcode]) : (Expr, Map[String, Value]) = {
    PC = 0
    backup = v1
    prog = pr
    
    prog.foreach(println)
    
    while (prog(PC) != Exit) {
      prog(PC).execute
      PC = PC + 1
    }
    
    if (register(BIND_SP_REGISTER) != 1) throw new Exception("extra bindings on the stack?")
    
    (retval, Map() ++ bindStack(0))
  }

}