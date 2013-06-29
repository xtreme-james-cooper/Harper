package cha11

import main.Parser
import main.Parser.{ pLit, pIdent, pNum }

object ExprParser {

  private val numTyParser : Parser[Type] = pLit("Num") map (_ => NumTy)
  private val arrTyParser : Parser[Type] =
    for {
      _ <- pLit("(")
      t1 <- tyParser
      _ <- pLit("-")
      _ <- pLit(">")
      t2 <- tyParser
      _ <- pLit(")")
    } yield ArrTy(t1, t2)
  private val prodParser : Parser[Type] =
    for {
      _ <- pLit("(")
      t1 <- tyParser
      _ <- pLit(",")
      t2 <- tyParser
      _ <- pLit(")")
    } yield ProdTy(t1, t2)
  private val unitParser : Parser[Type] = pLit("Unit") map (_ => UnitTy)

  private val tyParser : Parser[Type] = numTyParser || arrTyParser || prodParser || unitParser

  private val varParser : Parser[Expr] = pIdent map (x => Var(x))
  private val numParser : Parser[Expr] = pNum map (n => (0 until n).foldLeft(Z : Expr)((k, _) => S(k)))
  private val sParser : Parser[Expr] =
    for {
      _ <- pLit("S")
      _ <- pLit("(")
      e <- exprParser
      _ <- pLit(")")
    } yield S(e)
  private val letParser : Parser[Expr] =
    for {
      _ <- pLit("let")
      n <- pIdent
      _ <- pLit("be")
      d <- exprParser
      _ <- pLit("in")
      b <- exprParser
    } yield Let(d, n, b)
  private val apParser : Parser[Expr] =
    for {
      _ <- pLit("(")
      e1 <- exprParser
      e2 <- exprParser
      _ <- pLit(")")
    } yield Ap(e1, e2)
  private val fundefParser : Parser[Expr] =
    for {
      _ <- pLit("fun")
      f <- pIdent
      _ <- pLit("(")
      x <- pIdent
      _ <- pLit(":")
      t1 <- tyParser
      _ <- pLit(")")
      _ <- pLit(":")
      t2 <- tyParser
      _ <- pLit("=")
      e2 <- exprParser
      _ <- pLit("in")
      e <- exprParser
    } yield Let(Fix(ArrTy(t1, t2), f, (Lam(t1, x, e2))), f, e)
  private val lamParser : Parser[Expr] =
    for {
      _ <- pLit("\\")
      x <- pIdent
      _ <- pLit(":")
      t <- tyParser
      _ <- pLit(".")
      e <- exprParser
    } yield Lam(t, x, e)
  private val ifzParser : Parser[Expr] =
    for {
      _ <- pLit("ifz")
      e <- exprParser
      _ <- pLit("{")
      _ <- pLit("0")
      _ <- pLit("=")
      _ <- pLit(">")
      e0 <- exprParser
      _ <- pLit("|")
      _ <- pLit("S")
      _ <- pLit("(")
      x <- pIdent
      _ <- pLit(")")
      _ <- pLit("=")
      _ <- pLit(">")
      e1 <- exprParser
      _ <- pLit("}")
    } yield IfZ(e, e0, x, e1)
  private val fixParser : Parser[Expr] =
    for {
      _ <- pLit("fix")
      x <- pIdent
      _ <- pLit(":")
      t <- tyParser
      _ <- pLit("is")
      e <- exprParser
    } yield Fix(t, x, e)
  private val pairParser : Parser[Expr] =
    for {
      _ <- pLit("(")
      e1 <- exprParser
      _ <- pLit(",")
      e2 <- exprParser
      _ <- pLit(")")
    } yield Pair(e1, e2)
  private val prlParser : Parser[Expr] =
    for {
      _ <- pLit("projl")
      e <- exprParser
    } yield PrL(e)
  private val prrParser : Parser[Expr] =
    for {
      _ <- pLit("projr")
      e <- exprParser
    } yield PrR(e)
  private val trivParser : Parser[Expr] =
    for {
      _ <- pLit("(")
      _ <- pLit(")")
    } yield Triv

  val exprParser : Parser[Expr] =
    varParser || numParser || sParser || letParser || apParser || fundefParser || lamParser || ifzParser || fixParser || pairParser ||
      prlParser || prrParser || trivParser

}