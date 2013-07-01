package cha07

import main.Parser
import main.Parser.{ pLit, pIdent, pNum, pSat }

object ExprParser {

  val varParser : Parser[Expr] = pIdent map (x => Var(x))
  val numParser : Parser[Expr] = pNum map (n => Num(n))
  val strParser : Parser[Expr] =
    for {
      _ <- pLit("\"")
      e <- pSat(_ => true)
      _ <- pLit("\"")
    } yield Str(e)
  val plusParser : Parser[Expr] =
    for {
      _ <- pLit("(")
      e1 <- exprParser
      _ <- pLit("+")
      e2 <- exprParser
      _ <- pLit(")")
    } yield Plus(e1, e2)
  val timesParser : Parser[Expr] =
    for {
      _ <- pLit("(")
      e1 <- exprParser
      _ <- pLit("*")
      e2 <- exprParser
      _ <- pLit(")")
    } yield Times(e1, e2)
  val catParser : Parser[Expr] =
    for {
      _ <- pLit("(")
      e1 <- exprParser
      _ <- pLit("^")
      e2 <- exprParser
      _ <- pLit(")")
    } yield Cat(e1, e2)
  val lenParser : Parser[Expr] =
    for {
      _ <- pLit("|")
      e <- exprParser
      _ <- pLit("|")
    } yield Len(e)
  val letParser : Parser[Expr] =
    for {
      _ <- pLit("let")
      n <- pIdent
      _ <- pLit("be")
      d <- exprParser
      _ <- pLit("in")
      b <- exprParser
    } yield Let(d, n, b)

  val exprParser : Parser[Expr] =
    varParser || numParser || strParser || plusParser || timesParser || catParser || lenParser || letParser

}