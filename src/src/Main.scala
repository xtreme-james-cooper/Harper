package src

import interpreter.Evaluator
import interpreter.Typechecker
import parser.ExprParser

object Main {

  def main(args : Array[String]) : Unit = {

    test("Z")
    test("S(S(Z))")
    test("ifz S(Z) {Z => Z; S(k) => S(S(k))}")

  }

  def test(progs : String) {
    println("prog: " + progs)
    val prog = ExprParser.parse(progs)
    println("parse: " + prog)
    val typ = Typechecker.typecheck(prog)
    println("type: " + typ)
    val intVal = Evaluator.eval(prog)
    println("value" + ": " + intVal)
    println("-----------------------------")
  }

}