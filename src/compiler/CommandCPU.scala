package compiler

object CommandCPU {

  var PC : Int = 0
  var prog : List[CommandOpcode] = null

  val register : Array[Int] = Array.ofDim(32)

  var retval : Value = null

  var env : List[Map[String, Value]] = null

  var mem : List[(String, Value)] = null
  
  var subdefs : List[ExprOpcode] = null
  
  def run(pr : List[CommandOpcode], e : List[Map[String, Value]], s : List[ExprOpcode]) : Value = {
    PC = 0

    env = e
    mem = Nil
    subdefs = s
    
    prog = pr

    while (prog(PC) != CmdExit) {

      //      println("executing line " + PC + " " + prog(PC) + " " + retval)

      prog(PC).execute
      PC = PC + 1
    }

    retval
  }

  def goto(l : String) : Unit = { //TODO do search better
    //    println("looking for " + l)

    PC = 0
    while (prog(PC) != CmdLabel(l)) {
      PC = PC + 1
    }
  }

}