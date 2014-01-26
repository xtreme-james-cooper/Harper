package cha08

import org.junit.Assert._
import org.junit.Test
import Evaluator._
import main.GeneralTestSuite
import Typechecker.UnboundVariable

class TestEvaluator extends GeneralTestSuite {

  @Test
  def testSubstVar : Unit = {
    assertEquals(Num(3), subst(NumVal(3), "x")(Var("x")))
    assertEquals(Var("y"), subst(NumVal(3), "x")(Var("y")))
  }

  @Test
  def testSubstNum : Unit = {
    assertEquals(Num(5), subst(NumVal(3), "x")(Num(5)))
  }

  @Test
  def testSubstStr : Unit = {
    assertEquals(Str("k"), subst(NumVal(3), "x")(Str("k")))
  }

  @Test
  def testSubstPlus : Unit = {
    assertEquals(Plus(Num(3), Num(3)), subst(NumVal(3), "x")(Plus(Var("x"), Var("x"))))
    assertEquals(Plus(Var("y"), Num(3)), subst(NumVal(3), "x")(Plus(Var("y"), Var("x"))))
    assertEquals(Plus(Var("y"), Var("y")), subst(NumVal(3), "x")(Plus(Var("y"), Var("y"))))
  }

  @Test
  def testSubstTimes : Unit = {
    assertEquals(Times(Num(3), Num(3)), subst(NumVal(3), "x")(Times(Var("x"), Var("x"))))
    assertEquals(Times(Var("y"), Num(3)), subst(NumVal(3), "x")(Times(Var("y"), Var("x"))))
    assertEquals(Times(Var("y"), Var("y")), subst(NumVal(3), "x")(Times(Var("y"), Var("y"))))
  }

  @Test
  def testSubstCat : Unit = {
    assertEquals(Cat(Num(3), Num(3)), subst(NumVal(3), "x")(Cat(Var("x"), Var("x"))))
    assertEquals(Cat(Var("y"), Num(3)), subst(NumVal(3), "x")(Cat(Var("y"), Var("x"))))
    assertEquals(Cat(Var("y"), Var("y")), subst(NumVal(3), "x")(Cat(Var("y"), Var("y"))))
  }

  @Test
  def testSubstLen : Unit = {
    assertEquals(Len(Num(3)), subst(NumVal(3), "x")(Len(Var("x"))))
    assertEquals(Len(Var("y")), subst(NumVal(3), "x")(Len(Var("y"))))
  }

  @Test
  def testSubstLet : Unit = {
    assertEquals(Let(Num(3), "y", Var("y")), subst(NumVal(3), "x")(Let(Var("x"), "y", Var("y"))))
    assertEquals(Let(Num(3), "y", Plus(Var("y"), Num(3))), subst(NumVal(3), "x")(Let(Var("x"), "y", Plus(Var("y"), Var("x")))))
    assertEquals(Let(Num(3), "x", Var("y")), subst(NumVal(3), "x")(Let(Var("x"), "x", Var("y"))))
    assertEquals(Let(Num(3), "x", Plus(Var("y"), Var("x"))), subst(NumVal(3), "x")(Let(Var("x"), "x", Plus(Var("y"), Var("x")))))
    assertEquals(Let(Num(3), "y", Let(Num(4), "x", Var("x"))), subst(NumVal(3), "x")(Let(Var("x"), "y", Let(Num(4), "x", Var("x")))))
  }

  @Test
  def testEvalExpr : Unit = {
    assertThrows(UnboundVariable("x"), evalExpr(Var("x")))
    assertEquals(NumVal(3), evalExpr(Num(3)))
    assertEquals(StrVal("a"), evalExpr(Str("a")))
    assertEquals(NumVal(5), evalExpr(Plus(Num(3), Num(2))))
    assertEquals(NumVal(9), evalExpr(Plus(Num(3), Plus(Num(2), Num(4)))))
    assertEquals(NumVal(6), evalExpr(Times(Num(3), Num(2))))
    assertEquals(NumVal(18), evalExpr(Times(Num(3), Plus(Num(2), Num(4)))))
    assertEquals(StrVal("ab"), evalExpr(Cat(Str("a"), Str("b"))))
    assertEquals(StrVal("abc"), evalExpr(Cat(Str("a"), Cat(Str("b"), Str("c")))))
    assertEquals(NumVal(3), evalExpr(Len(Str("abc"))))
    assertEquals(NumVal(6), evalExpr(Times(Num(3), Len(Str("ab")))))
    assertEquals(NumVal(3), evalExpr(Let(Num(3), "x", Var("x"))))
    assertEquals(NumVal(5), evalExpr(Let(Plus(Num(3), Num(2)), "x", Var("x"))))
    assertEquals(NumVal(5), evalExpr(Let(Num(3), "x", Plus(Var("x"), Num(2)))))
    assertEquals(NumVal(5), evalExpr(Let(Num(3), "x", Let(Var("x"), "y", Plus(Var("y"), Num(2))))))
    assertEquals(NumVal(6), evalExpr(Let(Num(3), "x", Let(Plus(Var("x"), Num(1)), "x", Plus(Var("x"), Num(2))))))
  }

}