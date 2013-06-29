package main

import org.junit.Assert._
import org.junit.Test

class TestParser {

  @Test
  def testPEmpty : Unit = {
    val p : Parser[Unit] = Parser.pEmpty
    assertEquals(List(((), Nil)), p.run(Nil))
    assertEquals(List(((), List("hello"))), p.run(List("hello")))
    assertEquals(List(((), List("hello", "goodbye"))), p.run(List("hello", "goodbye")))
  }

  @Test
  def testPSatDifferentArgs : Unit = {
    val p : Parser[String] = Parser.pSat(_ == "hello")
    assertEquals(Nil, p.run(Nil))
    assertEquals(Nil, p.run(List("goodbye")))
    assertEquals(List(("hello", Nil)), p.run(List("hello")))
    assertEquals(List(("hello", List("goodbye"))), p.run(List("hello", "goodbye")))
    assertEquals(Nil, p.run(List("goodbye", "hello")))
  }

  @Test
  def testPSatDeferentPredicates : Unit = {
    assertEquals(Nil, Parser.pSat(_.head.isUpper).run(List("hello")))
    assertEquals(List(("Hello", Nil)), Parser.pSat(_.head.isUpper).run(List("Hello")))
    assertEquals(Nil, Parser.pSat(_.length == 3).run(List("goodbye")))
    assertEquals(List(("the", Nil)), Parser.pSat(_.length == 3).run(List("the")))
    assertEquals(List(("325", Nil)), Parser.pSat(_.forall(_.isDigit)).run(List("325")))
  }

  @Test
  def testPLit : Unit = {
    val p : Parser[String] = Parser.pLit("hello")
    assertEquals(Nil, p.run(Nil))
    assertEquals(Nil, p.run(List("goodbye")))
    assertEquals(List(("hello", Nil)), p.run(List("hello")))
    assertEquals(List(("hello", List("goodbye"))), p.run(List("hello", "goodbye")))
    assertEquals(Nil, p.run(List("goodbye", "hello")))
  }

  @Test
  def testPIdent : Unit = {
    val p : Parser[String] = Parser.pIdent
    assertEquals(Nil, p.run(Nil))
    assertEquals(Nil, p.run(List("Goodbye")))
    assertEquals(List(("_hello", Nil)), p.run(List("_hello")))
    assertEquals(Nil, p.run(List("34num")))
    assertEquals(List(("num34", Nil)), p.run(List("num34")))
    assertEquals(List(("s*^$$^V<CV<HC", Nil)), p.run(List("s*^$$^V<CV<HC")))
    assertEquals(List(("hello", List("goodbye"))), p.run(List("hello", "goodbye")))
  }

  @Test
  def testPEnd : Unit = {
    val p : Parser[Unit] = Parser.pEnd
    assertEquals(List(((), Nil)), p.run(Nil))
    assertEquals(Nil, p.run(List("goodbye")))
    assertEquals(Nil, p.run(List("hello", "goodbye")))
  }

  @Test
  def testOr : Unit = {
    val p : Parser[String] = Parser.pLit("hello") || Parser.pLit("goodbye")
    assertEquals(Nil, p.run(List("blah")))
    assertEquals(List(("hello", Nil)), p.run(List("hello")))
    assertEquals(List(("goodbye", Nil)), p.run(List("goodbye")))
    assertEquals(List(("hello", List("goodbye"))), p.run(List("hello", "goodbye")))
  }

  @Test
  def testFlatMap : Unit = {
    val p : Parser[String] = Parser.pIdent.flatMap(id => Parser.pLit(id))
    assertEquals(Nil, p.run(List("hello")))
    assertEquals(Nil, p.run(List("hello", "goodbye")))
    assertEquals(List(("hello", Nil)), p.run(List("hello", "hello")))
    assertEquals(List(("hello", List("goodbye"))), p.run(List("hello", "hello", "goodbye")))
    assertEquals(Nil, p.run(List("hello", "goodbye", "hello")))
  }

  @Test
  def testMap : Unit = {
    val p : Parser[String] = Parser.pIdent.map(id => id.take(3))
    assertEquals(Nil, p.run(Nil))
    assertEquals(List(("hel", Nil)), p.run(List("hello")))
    assertEquals(List(("hel", List("goodbye"))), p.run(List("hello", "goodbye")))
    assertEquals(List(("goo", List("hello"))), p.run(List("goodbye", "hello")))
  }

  @Test
  def testWithFilter : Unit = {
    val p : Parser[String] = Parser.pIdent.withFilter(id => id.length == 5)
    assertEquals(Nil, p.run(Nil))
    assertEquals(List(("hello", Nil)), p.run(List("hello")))
    assertEquals(List(("hello", List("goodbye"))), p.run(List("hello", "goodbye")))
    assertEquals(Nil, p.run(List("goodbye")))
    assertEquals(Nil, p.run(List("goodbye", "hello")))
  }

  @Test
  def testStar : Unit = {
    val p : Parser[List[String]] = Parser.pLit("hello").*
    assertEquals(List((Nil, Nil)), p.run(Nil))
    assertEquals(List((Nil, List("goodbye"))), p.run(List("goodbye")))
    assertEquals(List((Nil, List("goodbye", "hello"))), p.run(List("goodbye", "hello")))
    assertEquals(List((List("hello"), List("goodbye", "hello")), (Nil, List("hello", "goodbye", "hello"))),
      p.run(List("hello", "goodbye", "hello")))
    assertEquals(
      List(
        (List("hello", "hello"), List("goodbye", "hello")),
        (List("hello"), List("hello", "goodbye", "hello")),
        (Nil, List("hello", "hello", "goodbye", "hello"))),
      p.run(List("hello", "hello", "goodbye", "hello")))
    assertEquals(
      List(
        (List("hello", "hello", "hello"), List("goodbye", "hello")),
        (List("hello", "hello"), List("hello", "goodbye", "hello")),
        (List("hello"), List("hello", "hello", "goodbye", "hello")),
        (Nil, List("hello", "hello", "hello", "goodbye", "hello"))),
      p.run(List("hello", "hello", "hello", "goodbye", "hello")))
  }

  @Test
  def testPlus : Unit = {
    val p : Parser[List[String]] = Parser.pLit("hello").+
    assertEquals(Nil, p.run(Nil))
    assertEquals(Nil, p.run(List("goodbye")))
    assertEquals(Nil, p.run(List("goodbye", "hello")))
    assertEquals(List((List("hello"), List("goodbye", "hello"))), p.run(List("hello", "goodbye", "hello")))
    assertEquals(
      List(
        (List("hello", "hello"), List("goodbye", "hello")),
        (List("hello"), List("hello", "goodbye", "hello"))),
      p.run(List("hello", "hello", "goodbye", "hello")))
    assertEquals(
      List(
        (List("hello", "hello", "hello"), List("goodbye", "hello")),
        (List("hello", "hello"), List("hello", "goodbye", "hello")),
        (List("hello"), List("hello", "hello", "goodbye", "hello"))),
      p.run(List("hello", "hello", "hello", "goodbye", "hello")))
  }

  @Test
  def testQuestionMark : Unit = {
    val p : Parser[Option[String]] = Parser.pLit("hello").?
    assertEquals(List((None, Nil)), p.run(Nil))
    assertEquals(List((None, List("goodbye"))), p.run(List("goodbye")))
    assertEquals(List((None, List("goodbye", "hello"))), p.run(List("goodbye", "hello")))
    assertEquals(List((Some("hello"), List("goodbye", "hello")), (None, List("hello", "goodbye", "hello"))), p.run(List("hello", "goodbye", "hello")))
  }

  @Test
  def testTokenize : Unit = {
    assertEquals(Nil, Parser.tokenize(""))
    assertEquals(Nil, Parser.tokenize("   \t \n   "))
    assertEquals(List("word"), Parser.tokenize("word"))
    assertEquals(List("word"), Parser.tokenize("   \nword  \t"))
    assertEquals(List("word", "other", "word"), Parser.tokenize("   \nword other\nword \t"))
    assertEquals(List("digits", "3523235", "symbols", "^", "$", "*", "^", "$", "*", "both", "vdsds656", "$", "#", "%", "^", "#"),
      Parser.tokenize("digits 3523235 symbols ^$*^$* both vdsds656$#%^#"))
  }

  @Test
  def testParse : Unit = {
    assertEquals(Some(List("hello", "hello", "hello", "goodbye")), Parser.parse("hello hello hello goodbye",
      for {
        h <- Parser.pLit("hello").+
        g <- Parser.pLit("goodbye")
      } yield h :+ g))
    assertEquals(Some(List("hello", "hello", "goodbye")), Parser.parse("hello hello hello goodbye",
      for {
        h <- Parser.pLit("hello").+
        _ <- Parser.pLit("hello")
        g <- Parser.pLit("goodbye")
      } yield h :+ g))
    assertEquals(None, Parser.parse("hello hello hello goodbye",
      for {
        h <- Parser.pLit("goodbye").+
        _ <- Parser.pLit("hello")
        g <- Parser.pLit("goodbye")
      } yield h :+ g))
  }

}
