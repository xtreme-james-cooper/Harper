package cha07

import main.Parser
import main.Parser.{ pLit, pIdent, pNum }

object ExprParser {

  private val varParser : Parser[Expr] = pIdent map (x => Var(x))
  private val numParser : Parser[Expr] = pNum map (n => Num(n))
  private val strParser : Parser[Expr] =
    for {
      _ <- pLit("\"")
      e <- pIdent
      _ <- pLit("\"")
    } yield Str(e)
  private val plusParser : Parser[Expr] =
    for {
      _ <- pLit("(")
      e1 <- exprParser
      _ <- pLit("+")
      e2 <- exprParser
      _ <- pLit(")")
    } yield Plus(e1, e2)
  private val timesParser : Parser[Expr] =
    for {
      _ <- pLit("(")
      e1 <- exprParser
      _ <- pLit("*")
      e2 <- exprParser
      _ <- pLit(")")
    } yield Times(e1, e2)
  private val catParser : Parser[Expr] =
    for {
      _ <- pLit("(")
      e1 <- exprParser
      _ <- pLit("^")
      e2 <- exprParser
      _ <- pLit(")")
    } yield Cat(e1, e2)
  private val lenParser : Parser[Expr] =
    for { 
      _ <- pLit("|")
      e <- exprParser
      _ <- pLit("|")
    } yield Len(e)
  private val letParser : Parser[Expr] =
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