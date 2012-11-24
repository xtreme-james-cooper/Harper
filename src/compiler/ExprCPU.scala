package compiler

import model.Expr

object ExprCPU {

  var PC : Int = 0
  var prog : List[ExprOpcode] = null

  val register : Array[Int] = Array.ofDim(32)

  var retval : List[Value] = null

  var env : List[Map[String, Value]] = null

  var envTemp : Map[String, Value] = null

  var patReturn : (String, Map[String, Value]) = null

  var returnStack : List[String] = null

  def run(pr : List[ExprOpcode], m : List[Map[String, Value]]) : Value = {
    PC = 0
    env = m
    prog = pr
    retval = Nil
    returnStack = Nil

    while (prog(PC) != ExprExit) {
      println("executing line " + PC + " " + prog(PC) + " " + retval)

      prog(PC).execute
      PC = PC + 1
    }

    retval.head
  }

  def goto(l : String) : Unit = { //TODO do search better
//    println("looking for " + l)
    
    PC = 0
    while (prog(PC) != ExprLabel(l)) {
      PC = PC + 1
    }
  }

}