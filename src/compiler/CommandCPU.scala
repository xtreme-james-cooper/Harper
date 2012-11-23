package compiler

import model.Value

object CommandCPU {

  var PC : Int = 0
  var prog : List[CommandOpcode] = null

  val register : Array[Int] = Array.ofDim(32)

  var retval : Value = null

  def run(pr : List[CommandOpcode]) : Value = {
    PC = 0

    prog = pr

    //    prog.foreach(println)

    while (prog(PC) != Exit) {
      prog(PC).execute
      PC = PC + 1
    }

    retval
  }

}