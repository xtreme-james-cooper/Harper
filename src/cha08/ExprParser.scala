package cha08

import main.Parser
import main.Parser.{ pLit, pIdent, pNum, pSat }

object ExprParser {

  val numTyParser : Parser[Type] = pLit("Num") map (_ => NumTy)
  val strTyParser : Parser[Type] = pLit("Str") map (_ => StrTy)
  val arrTyParser : Parser[Type] =
    for {
      _ <- pLit("(")
      t1 <- tyParser
      _ <- pLit("-")
      _ <- pLit(">")
      t2 <- tyParser
      _ <- pLit(")")
    } yield ArrTy(t1, t2)

  val tyParser : Parser[Type] = numTyParser || strTyParser || arrTyParser

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
  val apParser : Parser[Expr] =
    for {
      _ <- pLit("(")
      e1 <- exprParser
      e2 <- exprParser
      _ <- pLit(")")
    } yield Ap(e1, e2)
  val fundefParser : Parser[Expr] =
    for {
      _ <- pLit("fun")
      f <- pIdent
      _ <- pLit("(")
      x <- pIdent
      _ <- pLit(":")
      t <- tyParser
      _ <- pLit(")")
      _ <- pLit("=")
      e2 <- exprParser
      _ <- pLit("in")
      e <- exprParser
    } yield Let(Lam(t, x, e2), f, e)
  val lamParser : Parser[Expr] =
    for {
      _ <- pLit("\\")
      x <- pIdent
      _ <- pLit(":")
      t <- tyParser
      _ <- pLit(".")
      e <- exprParser
    } yield Lam(t, x, e)

  val exprParser : Parser[Expr] =
    varParser || numParser || strParser || plusParser || timesParser || catParser || lenParser || letParser || apParser || fundefParser || lamParser

}