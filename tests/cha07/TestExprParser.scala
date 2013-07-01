package cha07

import org.junit.Assert._
import org.junit.Test
import main.Parser.parse

class TestExprParser {

  @Test
  def testVarParser : Unit = {
    assertEquals(None, parse("K", ExprParser.varParser))
    assertEquals(None, parse("3", ExprParser.varParser))
    assertEquals(None, parse("*", ExprParser.varParser))
    assertEquals(Some(Var("k")), parse("k", ExprParser.varParser))
    assertEquals(Some(Var("kpk")), parse("kpk", ExprParser.varParser))
  }

  @Test
  def testNumParser : Unit = {
    assertEquals(None, parse("K", ExprParser.numParser))
    assertEquals(None, parse("*", ExprParser.numParser))
    assertEquals(Some(Num(3)), parse("3", ExprParser.numParser))
    assertEquals(Some(Num(378)), parse("378", ExprParser.numParser))
  }

  @Test
  def testStrParser : Unit = {
    assertEquals(None, parse("K", ExprParser.strParser))
    assertEquals(None, parse("3", ExprParser.strParser))
    assertEquals(None, parse("*", ExprParser.strParser))
    assertEquals(Some(Str("K")), parse("\"K\"", ExprParser.strParser))
    assertEquals(Some(Str("3")), parse("\"3\"", ExprParser.strParser))
    assertEquals(Some(Str("*")), parse("\"*\"", ExprParser.strParser))
    assertEquals(Some(Str("Kasvvassva")), parse("\"Kasvvassva\"", ExprParser.strParser))
  }

  @Test
  def testPlusParser : Unit = {
    assertEquals(None, parse("3 + k", ExprParser.plusParser))
    assertEquals(Some(Plus(Num(3), Var("k"))), parse("(3 + k)", ExprParser.plusParser))
    assertEquals(Some(Plus(Num(3), Plus(Var("k"), Num(5)))), parse("(3 + (k + 5))", ExprParser.plusParser))
    assertEquals(Some(Plus(Plus(Num(3), Var("p")), Plus(Var("k"), Num(5)))), parse("((3 + p) + (k + 5))", ExprParser.plusParser))
  }

  @Test
  def testTimesParser : Unit = {
    assertEquals(None, parse("3 * k", ExprParser.timesParser))
    assertEquals(Some(Times(Num(3), Var("k"))), parse("(3 * k)", ExprParser.timesParser))
    assertEquals(Some(Times(Num(3), Times(Var("k"), Num(5)))), parse("(3 * (k * 5))", ExprParser.timesParser))
    assertEquals(Some(Times(Plus(Num(3), Var("p")), Plus(Var("k"), Num(5)))), parse("((3 + p) * (k + 5))", ExprParser.timesParser))
  }

  @Test
  def testCatParser : Unit = {
    assertEquals(None, parse("3 ^ k", ExprParser.catParser))
    assertEquals(Some(Cat(Num(3), Var("k"))), parse("(3 ^ k)", ExprParser.catParser))
    assertEquals(Some(Cat(Num(3), Cat(Var("k"), Num(5)))), parse("(3 ^ (k ^ 5))", ExprParser.catParser))
    assertEquals(Some(Cat(Plus(Num(3), Var("p")), Plus(Var("k"), Num(5)))), parse("((3 + p) ^ (k + 5))", ExprParser.catParser))
  }

  @Test
  def testLenParser : Unit = {
    assertEquals(None, parse("|3 ^ k|", ExprParser.lenParser))
    assertEquals(Some(Len(Var("k"))), parse("|k|", ExprParser.lenParser))
    assertEquals(Some(Len(Cat(Num(3), Var("k")))), parse("|(3 ^ k)|", ExprParser.lenParser))
  }

  @Test
  def testLetParser : Unit = {
    assertEquals(None, parse("let (x + y) be 45 in x", ExprParser.letParser))
    assertEquals(Some(Let(Num(45), "x", Var("x"))), parse("let x be 45 in x", ExprParser.letParser))
    assertEquals(Some(Let(Plus(Num(45), Var("k")), "x", Var("x"))), parse("let x be (45 + k) in x", ExprParser.letParser))
    assertEquals(Some(Let(Num(45), "x", Cat(Var("x"), Str("4")))), parse("let x be 45 in (x ^ \"4\")", ExprParser.letParser))
    assertEquals(Some(Let(Plus(Num(45), Var("k")), "x", Cat(Var("x"), Str("4")))), parse("let x be (45 + k) in (x ^ \"4\")", ExprParser.letParser))
  }

}