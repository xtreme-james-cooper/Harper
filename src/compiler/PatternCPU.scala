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

  var valTag : Int = 0
  
  val valStack : Array[Value] = Array.ofDim(1000) //TODO large enough?
  var valSP : Int = 0
  
  var backup : Value = null
  
  var v : Value = null

  var retval : Expr = null
  
  var matchRetval : Map[String, Value] = null
  
  val bindStack : Array[Map[String, Value]] = Array.ofDim(1000) //TODO large enough?
  var bindSP : Int = 0

  def run(v1 : Value, pr : List[PatternOpcode]) : (Expr, Map[String, Value]) = {
    PC = 0
    backup = v1
    prog = pr
    
//    prog.foreach(println)
    
    while (prog(PC) != Exit) {
      prog(PC).execute
      PC = PC + 1
      
//      println("At " + PC + "(" + prog(PC) + ") with value " + v + " loadstk " + loadStack + " matchretval " + matchRetval + " mrvstk" + matchRetvalStack)
    }
    (retval, matchRetval)
  }

}