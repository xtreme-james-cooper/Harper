package src

import interpreter.Evaluator
import interpreter.Typechecker
import parser.ProgParser

object Main {

  def main(args : Array[String]) : Unit = {

    test("Z")
    test("S(S(Z))")
    test("case S(Z) of {Z => Z; S(k) => S(S(k))}")
    test("(\\x:Nat.x S(Z))")
    test("fix double:(Nat=>Nat) in \\x:Nat.case x of {Z => Z; S(k) => S(S((double k)))}")
    test("(fix double:(Nat=>Nat) in \\x:Nat.case x of {Z => Z; S(k) => S(S((double k)))} S(S(S(Z))))")
    test("(\\x:Unit.Z ())")
    test("(fix swap:((Nat, Unit)=>(Unit, Nat)) in \\x:(Nat, Unit) . (projR x, projL x) (S(S(Z)), ()))")
    test("(\\x:(Unit+Nat).case x of {inL x => Z; inR x => S(x)} inL:(Unit+Nat) () )")
    test("(\\x:(Unit+Nat).case x of {inL x => Z; inR x => S(x)} inR:(Unit+Nat) S(Z))")
    test("case (S(Z), inL : (Unit+Nat) ()) of { (n, inL _) => S(S(n)) ; (S(Z), inR Z) => Z }")
    test("case (S(Z), inR : (Unit+Nat) Z) of { (n, inL _) => S(S(n)) ; (S(Z), inR Z) => Z }")
    
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