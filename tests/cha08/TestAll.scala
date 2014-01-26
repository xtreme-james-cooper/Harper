package cha08

import org.junit.Assert._
import org.junit.Test
import main.Parser.parse

class TestAll {

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
    parse(progs, ExprParser.exprParser) match {
      case None => fail
      case Some(prog) => {
        assertEquals(eType, Typechecker.typecheck(prog))
        assertEquals(eVal, Evaluator.evalExpr(prog))
      }
    }
  }

}