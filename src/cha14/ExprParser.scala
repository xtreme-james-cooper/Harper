package cha14

import main.Parser
import main.Parser.{ pLit, pIdent, pNum }

object ExprParser {

  private val varTyParser : Parser[Type] = pIdent map (x => VarTy(x))
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
  private val voidParser : Parser[Type] = pLit("Void") map (_ => VoidTy)
  private val sumParser : Parser[Type] =
    for {
      _ <- pLit("(")
      t1 <- tyParser
      _ <- pLit("+")
      t2 <- tyParser
      _ <- pLit(")")
    } yield SumTy(t1, t2)

  private val tyParser : Parser[Type] = numTyParser || arrTyParser || prodParser || unitParser || sumParser || voidParser || varTyParser

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
  private val abortParser : Parser[Expr] =
    for {
      _ <- pLit("abort")
      _ <- pLit(":")
      t <- tyParser
      _ <- pLit("(")
      e <- exprParser
      _ <- pLit(")")
    } yield Abort(t, e)
  private val inlParser : Parser[Expr] =
    for {
      _ <- pLit("inl")
      _ <- pLit(":")
      t <- tyParser
      _ <- pLit("(")
      e <- exprParser
      _ <- pLit(")")
    } yield InL(t, e)
  private val inrParser : Parser[Expr] =
    for {
      _ <- pLit("inr")
      _ <- pLit(":")
      t <- tyParser
      _ <- pLit("(")
      e <- exprParser
      _ <- pLit(")")
    } yield InR(t, e)
  private val matchParser : Parser[Expr] =
    for {
      _ <- pLit("case")
      e <- exprParser
      _ <- pLit("of")
      _ <- pLit("{")
      rs <- rulesParser
      _ <- pLit("}")
    } yield Match(e, rs)
  private val genericParser : Parser[Expr] =
    for { 
      _ <- pLit("map") 
      _ <- pLit(":") 
      _ <- pLit("(") 
      tx <- pIdent 
      _ <- pLit(".") 
      t <- tyParser 
      _ <- pLit(")")
      x <- pIdent
      _ <- pLit(":")
      xt <- tyParser 
      _ <- pLit(".")
      e0 <- exprParser
      e <- exprParser 
    } yield Generic(tx, t, x, xt, e0, e)

  val exprParser : Parser[Expr] =
    varParser || numParser || sParser || letParser || apParser || fundefParser || lamParser || fixParser || pairParser ||
      prlParser || prrParser || trivParser || abortParser || inlParser || inrParser || matchParser || genericParser

  private val wildParser : Parser[Pattern] = pLit("_") map (_ => WildPat)
  private val varPatParser : Parser[Pattern] = pIdent map (x => VarPat(x))
  private val zParser : Parser[Pattern] = pLit("Z") map (_ => ZPat)
  private val sPatParser : Parser[Pattern] =
    for {
      _ <- pLit("S")
      _ <- pLit("(")
      e <- patternParser
      _ <- pLit(")")
    } yield SPat(e)
  private val trivPatParser : Parser[Pattern] =
    for {
      _ <- pLit("(")
      _ <- pLit(")")
    } yield TrivPat
  private val pairPatParser : Parser[Pattern] = 
    for {
      _ <- pLit("(")
      p1 <- patternParser 
      _ <- pLit(",") 
      p2 <- patternParser 
      _ <- pLit(")")
    } yield PairPat(p1, p2)
  private val inLParser : Parser[Pattern] = 
    for {
      _ <- pLit("inl")
      e <- patternParser
    } yield InLPat(e)
  private val inRParser : Parser[Pattern] = 
    for {
      _ <- pLit("inr")
      e <- patternParser
    } yield InRPat(e)

  private val patternParser : Parser[Pattern] =
    wildParser || varPatParser || zParser || sPatParser || trivPatParser || pairPatParser || inLParser || inRParser

  private val ruleParser : Parser[(Pattern, Expr)] = for {
    p <- patternParser
    _ <- pLit("=")
    _ <- pLit(">")
    e <- exprParser
  } yield (p, e)

  val rulesParser : Parser[List[(Pattern, Expr)]] = ruleParser intersperse pLit("|")

}