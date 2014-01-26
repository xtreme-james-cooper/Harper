package cha08

import org.junit.Assert._
import org.junit.Test
import Typechecker._
import main.GeneralTestSuite

class TestTypechecker extends GeneralTestSuite {

  @Test
  def testExpectType : Unit = {
    assertEquals(3, expectType(StrTy, StrTy)(3))
    assertEquals("x", expectType(StrTy, StrTy)("x"))
    assertThrows(TypeMismatch(StrTy, NumTy), expectType(StrTy, NumTy)(3))
    assertThrows(UnboundVariable("p"), expectType(StrTy, StrTy)(throw UnboundVariable("p")))
  }

  @Test
  def testTypecheckExprStr : Unit = {
    assertEquals(StrTy, typecheckExpr(Map())(Str("t")))
    assertEquals(StrTy, typecheckExpr(Map("x" -> NumTy))(Str("t")))
  }

  @Test
  def testTypecheckExprNum : Unit = {
    assertEquals(NumTy, typecheckExpr(Map())(Num(5)))
    assertEquals(NumTy, typecheckExpr(Map("x" -> NumTy))(Num(5)))
  }

  @Test
  def testTypecheckExprVar : Unit = {
    assertEquals(StrTy, typecheckExpr(Map("x" -> StrTy))(Var("x")))
    assertEquals(NumTy, typecheckExpr(Map("x" -> NumTy))(Var("x")))
    assertThrows(UnboundVariable("x"), typecheckExpr(Map())(Var("x")))
  }

  @Test
  def testTypecheckExprPlus : Unit = {
    assertEquals(NumTy, typecheckExpr(Map())(Plus(Num(5), Num(7))))
    assertEquals(NumTy, typecheckExpr(Map("x" -> NumTy))(Plus(Num(5), Num(7))))
    assertEquals(NumTy, typecheckExpr(Map("x" -> NumTy))(Plus(Num(5), Var("x"))))
    assertThrows(TypeMismatch(NumTy, StrTy), typecheckExpr(Map())(Plus(Num(5), Str("7"))))
    assertThrows(TypeMismatch(NumTy, StrTy), typecheckExpr(Map("x" -> StrTy))(Plus(Num(5), Var("x"))))
  }

  @Test
  def testTypecheckExprTimes : Unit = {
    assertEquals(NumTy, typecheckExpr(Map())(Times(Num(5), Num(7))))
    assertEquals(NumTy, typecheckExpr(Map("x" -> NumTy))(Times(Num(5), Num(7))))
    assertEquals(NumTy, typecheckExpr(Map("x" -> NumTy))(Times(Num(5), Var("x"))))
    assertThrows(TypeMismatch(NumTy, StrTy), typecheckExpr(Map())(Times(Num(5), Str("7"))))
    assertThrows(TypeMismatch(NumTy, StrTy), typecheckExpr(Map("x" -> StrTy))(Times(Num(5), Var("x"))))
  }

  @Test
  def testTypecheckExprCat : Unit = {
    assertEquals(StrTy, typecheckExpr(Map())(Cat(Str("5"), Str("7"))))
    assertEquals(StrTy, typecheckExpr(Map("x" -> StrTy))(Cat(Str("5"), Str("7"))))
    assertEquals(StrTy, typecheckExpr(Map("x" -> StrTy))(Cat(Str("5"), Var("x"))))
    assertThrows(TypeMismatch(StrTy, NumTy), typecheckExpr(Map())(Cat(Num(5), Str("7"))))
    assertThrows(TypeMismatch(StrTy, NumTy), typecheckExpr(Map("x" -> NumTy))(Cat(Str("5"), Var("x"))))
  }

  @Test
  def testTypecheckExprLen : Unit = {
    assertEquals(NumTy, typecheckExpr(Map())(Len(Str("5"))))
    assertEquals(NumTy, typecheckExpr(Map("x" -> StrTy))(Len(Str("5"))))
    assertEquals(NumTy, typecheckExpr(Map("x" -> StrTy))(Len(Var("x"))))
    assertThrows(TypeMismatch(StrTy, NumTy), typecheckExpr(Map())(Len(Num(5))))
    assertThrows(TypeMismatch(StrTy, NumTy), typecheckExpr(Map("x" -> NumTy))(Len(Var("x"))))
  }

  @Test
  def testTypecheckExprLet : Unit = {
    assertEquals(NumTy, typecheckExpr(Map())(Let(Str("a"), "x", Num(4))))
    assertEquals(StrTy, typecheckExpr(Map())(Let(Str("a"), "x", Var("x"))))
    assertEquals(StrTy, typecheckExpr(Map("y" -> NumTy))(Let(Str("a"), "x", Var("x"))))
    assertEquals(NumTy, typecheckExpr(Map("y" -> NumTy))(Let(Str("a"), "x", Var("y"))))
    assertEquals(StrTy, typecheckExpr(Map("x" -> NumTy))(Let(Str("a"), "x", Var("x"))))
    assertThrows(UnboundVariable("x"), typecheckExpr(Map())(Let(Var("x"), "x", Var("x"))))
    assertThrows(UnboundVariable("x"), typecheckExpr(Map())(Let(Var("x"), "x", Num(3))))
    assertEquals(NumTy, typecheckExpr(Map("x" -> NumTy))(Let(Var("x"), "x", Var("x"))))
  }

  @Test
  def testTypecheck : Unit = {
    assertEquals(StrTy, typecheck(Str("t")))
    assertEquals(StrTy, typecheckExpr(Map("x" -> NumTy))(Str("t")))
    assertEquals(NumTy, typecheck(Num(5)))
    assertEquals(NumTy, typecheckExpr(Map("x" -> NumTy))(Num(5)))
    assertEquals(StrTy, typecheckExpr(Map("x" -> StrTy))(Var("x")))
    assertEquals(NumTy, typecheckExpr(Map("x" -> NumTy))(Var("x")))
    assertEquals(NumTy, typecheck(Plus(Num(5), Num(7))))
    assertEquals(NumTy, typecheckExpr(Map("x" -> NumTy))(Plus(Num(5), Num(7))))
    assertEquals(NumTy, typecheckExpr(Map("x" -> NumTy))(Plus(Num(5), Var("x"))))
    assertEquals(NumTy, typecheck(Times(Num(5), Num(7))))
    assertEquals(NumTy, typecheckExpr(Map("x" -> NumTy))(Times(Num(5), Num(7))))
    assertEquals(NumTy, typecheckExpr(Map("x" -> NumTy))(Times(Num(5), Var("x"))))
    assertEquals(StrTy, typecheck(Cat(Str("5"), Str("7"))))
    assertEquals(StrTy, typecheckExpr(Map("x" -> StrTy))(Cat(Str("5"), Str("7"))))
    assertEquals(StrTy, typecheckExpr(Map("x" -> StrTy))(Cat(Str("5"), Var("x"))))
    assertEquals(NumTy, typecheck(Len(Str("5"))))
    assertEquals(NumTy, typecheckExpr(Map("x" -> StrTy))(Len(Str("5"))))
    assertEquals(NumTy, typecheckExpr(Map("x" -> StrTy))(Len(Var("x"))))
    assertEquals(NumTy, typecheck(Let(Str("a"), "x", Num(4))))
    assertEquals(StrTy, typecheck(Let(Str("a"), "x", Var("x"))))
    assertThrows(UnboundVariable("x"), typecheck(Let(Var("x"), "x", Var("x"))))
    assertThrows(UnboundVariable("x"), typecheck(Let(Var("x"), "x", Num(3))))
  }

}