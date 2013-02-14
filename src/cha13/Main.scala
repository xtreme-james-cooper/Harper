package cha13

import all.Parser.parse

object Main {

  def runTests : Unit = {
    test("3", NumTy, SVal(SVal(SVal(ZVal))))
    test("let x be 4 in S(x)", NumTy, SVal(SVal(SVal(SVal(SVal(ZVal))))))
    test("let x be 4 in let x be S(S(x)) in S(S(S(x)))", NumTy, SVal(SVal(SVal(SVal(SVal(SVal(SVal(SVal(SVal(ZVal))))))))))
    test("\\x:Num.S(S(x))", ArrTy(NumTy, NumTy), LamVal(NumTy, "x", S(S(Var("x")))))
    test("let x be 4 in (\\x:Num.S(S(x)) x)", NumTy, SVal(SVal(SVal(SVal(SVal(SVal(ZVal)))))))
    test("let plustu be \\x:Num.S(S(x)) in let x be 4 in (plustu x)", NumTy, SVal(SVal(SVal(SVal(SVal(SVal(ZVal)))))))
    test("fun plustu(x:Num):Num = S(S(x)) in let x be 4 in (plustu x)", NumTy, SVal(SVal(SVal(SVal(SVal(SVal(ZVal)))))))
    test("case 2 of { Z => 0 | S(x) => S(S(x)) }", NumTy, SVal(SVal(SVal(ZVal))))
    test("case 0 of { Z => 1 | S(x) => S(S(x)) }", NumTy, SVal(ZVal))
    test("fix x:Num is 2", NumTy, SVal(SVal(ZVal)))
    test("fun dub(x : Num):Num = case x of { Z => 0 | S(x) => S(S((dub x))) } in (dub 4)", NumTy, SVal(SVal(SVal(SVal(SVal(SVal(SVal(SVal(ZVal)))))))))
    test("(3, 4)", ProdTy(NumTy, NumTy), PairVal(SVal(SVal(SVal(ZVal))), SVal(SVal(SVal(SVal(ZVal))))))
    test("(3, (1, 4))", ProdTy(NumTy, ProdTy(NumTy, NumTy)), PairVal(SVal(SVal(SVal(ZVal))), PairVal(SVal(ZVal), SVal(SVal(SVal(SVal(ZVal)))))))
    test("projl (3, (1, 4))", NumTy, SVal(SVal(SVal(ZVal))))
    test("projl projr (3, (1, 4))", NumTy, SVal(ZVal))
    test("()", UnitTy, TrivVal)
    test("projr (3, ())", UnitTy, TrivVal)
    test("projl (3, ())", NumTy, SVal(SVal(SVal(ZVal))))
    //cannot test abort because no terminating value exists
    //test("abort:Nat (fix x:Void is x)", Num, ZVal)
    test("inl : (Unit + Num) (())", SumTy(UnitTy, NumTy), InLVal(SumTy(UnitTy, NumTy), TrivVal))
    test("inr : (Unit + Num) (3)", SumTy(UnitTy, NumTy), InRVal(SumTy(UnitTy, NumTy), SVal(SVal(SVal(ZVal)))))
    test("case inr : (Unit + Num) (3) of { inl x => 0 | inr y => S(y) }", NumTy, SVal(SVal(SVal(SVal(ZVal)))))
    test("(\\x:(Unit + Num).case x of {inl x => 0 | inr x => S(x)} inl:(Unit + Num) (()) )", NumTy, ZVal)
    test("(\\x:(Unit + Num).case x of {inl x => 0 | inr x => S(x)} inr:(Unit + Num) (1))", NumTy, SVal(SVal(ZVal)))
    test("case (1, inl:(Unit+Num) (())) of { (n, inl _) => S(S(n)) | (S(Z), inr Z) => 0 }", NumTy, SVal(SVal(SVal(ZVal))))
    test("case (1, inr:(Unit+Num) (0)) of { (n, inl _) => S(S(n)) | (S(Z), inr Z) => 0 }", NumTy, ZVal)
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