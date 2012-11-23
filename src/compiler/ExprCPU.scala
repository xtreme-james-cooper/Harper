package compiler

import model.Expr

object ExprCPU {

  var PC : Int = 0
  var prog : List[ExprOpcode] = null

  val register : Array[Int] = Array.ofDim(32)

  var retval : List[Value] = null

  var lamStack : List[(String, Expr, Map[String, Value])] = null
  
  var env : List[Map[String, Value]] = null

  var envTemp : Map[String, Value] = null

  var patReturn : (Expr, Map[String, Value]) = null

  def run(pr : List[ExprOpcode], m : List[Map[String, Value]]) : Value = {
    PC = 0
    env = m
    prog = pr
    retval = Nil
    lamStack = Nil
    
    prog.foreach(println)

    while (prog(PC) != ExprExit) {
      prog(PC).execute
      PC = PC + 1
    }

    retval.head
  }

}