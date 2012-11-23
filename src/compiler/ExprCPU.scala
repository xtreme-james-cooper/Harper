package compiler

import model.Value

object ExprCPU {

  var PC : Int = 0
  var prog : List[ExprOpcode] = null

  val register : Array[Int] = Array.ofDim(32)

  var retval : List[Value] = Nil

  var env : List[Map[String, Value]] = null
  
  var envTemp : Map[String, Value] = null
  
  def run(pr : List[ExprOpcode], m : List[Map[String, Value]]) : Value = {
    PC = 0

    env = m
    
    prog = pr

    //    prog.foreach(println)

    while (prog(PC) != ExprExit) {
      prog(PC).execute
      PC = PC + 1
    }

    retval.head
  }

}