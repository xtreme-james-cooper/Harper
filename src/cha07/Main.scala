package cha07

import main.Parser.parse

object Main {

  def runTests : Unit = {
    test("3", NumTy, NumVal(3))
    test("\"blah\"", StrTy, StrVal("blah"))
    test("(3 + 4)", NumTy, NumVal(7))
    test("((3 * 5) + 6)", NumTy, NumVal(21))
    test("(\"x\" ^ \"y\")", StrTy, StrVal("xy"))
    test("(|(\"x\" ^ \"y\")| + 4)", NumTy, NumVal(6))
    test("let x be 4 in (3 + x)", NumTy, NumVal(7))
    test("let x be 4 in let x be (x * 2) in (3 + x)", NumTy, NumVal(11))
  }

  def test(progs : String, eType : Type, eVal : Value) : Unit = {
    println("prog: " + progs)
    val prog = parse(progs, ExprParser.exprParser)
    println("parse: " + prog)
    val typ = Typechecker.typecheck(prog)
    if (typ != eType) throw new Exception("expected " + eType + " but got " + typ)
    println("type: " + typ)
    val intVal = Evaluator.evalExpr(prog)
    if (intVal != eVal) throw new Exception("for interpreted expected " + eVal + " but got " + intVal)
    println("value" + ": " + intVal)
    println("-----------------------------")
  }

}