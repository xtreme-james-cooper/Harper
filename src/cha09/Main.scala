package cha09

import main.Parser.parse

object Main {

  def runTests : Unit = {
    test("3", NumTy, SVal(SVal(SVal(ZVal))))
    test("let x be 4 in S(x)", NumTy, SVal(SVal(SVal(SVal(SVal(ZVal))))))
    test("let x be 4 in let x be S(S(x)) in S(S(S(x)))", NumTy, SVal(SVal(SVal(SVal(SVal(SVal(SVal(SVal(SVal(ZVal))))))))))
    test("\\x:Num.S(S(x))", ArrTy(NumTy, NumTy), LamVal(NumTy, "x", S(S(Var("x")))))
    test("let x be 4 in (\\x:Num.S(S(x)) x)", NumTy, SVal(SVal(SVal(SVal(SVal(SVal(ZVal)))))))
    test("let plustu be \\x:Num.S(S(x)) in let x be 4 in (plustu x)", NumTy, SVal(SVal(SVal(SVal(SVal(SVal(ZVal)))))))
    test("fun plustu(x:Num) = S(S(x)) in let x be 4 in (plustu x)", NumTy, SVal(SVal(SVal(SVal(SVal(SVal(ZVal)))))))
    test("rec 2 { 0 => 0 | S(x) with y => S(S(y)) }", NumTy, SVal(SVal(SVal(SVal(ZVal)))))
    test("fun dub(x : Num) = rec x { 0 => 0 | S(x) with y => S(S(y)) } in dub", ArrTy(NumTy, NumTy),
        LamVal(NumTy, "x", Rec(Z, "x", "y", S(S(Var("y"))), Var("x"))))
    test("fun dub(x : Num) = rec x { 0 => 0 | S(x) with y => S(S(y)) } in (dub 4)", NumTy, SVal(SVal(SVal(SVal(SVal(SVal(SVal(SVal(ZVal)))))))))
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