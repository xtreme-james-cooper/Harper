package src

import interpreter.Evaluator
import interpreter.Typechecker
import parser.ProgParser

object Main {

  def main(args : Array[String]) : Unit = {

    test("Z")
    test("S(S(Z))")
    test("ifz S(Z) {Z => Z; S(k) => S(S(k))}")
    test("(\\x:Nat.x S(Z))")
    test("fix double:(Nat=>Nat) in \\x:Nat.ifz x {Z => Z; S(k) => S(S((double k)))}")
    test("(fix double:(Nat=>Nat) in \\x:Nat.ifz x {Z => Z; S(k) => S(S((double k)))} S(S(S(Z))))")


  }

  def test(progs : String) {
    println("prog: " + progs)
    val prog = ProgParser.parse(progs)
    println("parse: " + prog)
    val typ = Typechecker.typecheck(prog)
    println("type: " + typ)
    val intVal = Evaluator.eval(prog)
    println("value" + ": " + intVal)
    println("-----------------------------")
  }

}