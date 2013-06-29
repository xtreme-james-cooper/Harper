package cha08

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
    test("\\x:Num.(x * 2)", ArrTy(NumTy, NumTy), LamVal(NumTy, "x", Times(Var("x"), Num(2))))
    test("let x be 4 in (\\x:Num.(x * 2) x)", NumTy, NumVal(8))
    test("let dub be \\x:Num.(x * 2) in let x be 4 in (dub x)", NumTy, NumVal(8))
    test("fun dub(x:Num) = (x * 2) in let x be 4 in (dub x)", NumTy, NumVal(8))

  }

  def test(progs : String, eType : Type, eVal : Value) : Unit = {
    println("prog: " + progs)
    val prog = parse(progs, ExprParser.exprParser).getOrElse(throw new Exception("no full parse of " + progs))
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