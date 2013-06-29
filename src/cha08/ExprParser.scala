package cha08

import main.Parser
import main.Parser.{ pLit, pIdent, pNum }

object ExprParser {

  private val numTyParser : Parser[Type] = pLit("Num") appl (_ => NumTy)
  private val strTyParser : Parser[Type] = pLit("Str") appl (_ => StrTy)
  private val arrTyParser : Parser[Type] = pLit("(") thenJ tyParser thenK pLit("-") thenK pLit(">") thenS tyParser thenK pLit(")") appl
    ({ case (t1, t2) => ArrTy(t1, t2) })

  private val tyParser : Parser[Type] = numTyParser or strTyParser or arrTyParser

  private val varParser : Parser[Expr] = pIdent appl (x => Var(x))
  private val numParser : Parser[Expr] = pNum appl (n => Num(n))
  private val strParser : Parser[Expr] = pLit("\"") thenJ pIdent thenK pLit("\"") appl (e => Str(e))
  private val plusParser : Parser[Expr] =
    pLit("(") thenJ exprParser thenK pLit("+") thenS exprParser thenK pLit(")") appl ({ case (e1, e2) => Plus(e1, e2) })
  private val timesParser : Parser[Expr] =
    pLit("(") thenJ exprParser thenK pLit("*") thenS exprParser thenK pLit(")") appl ({ case (e1, e2) => Times(e1, e2) })
  private val catParser : Parser[Expr] =
    pLit("(") thenJ exprParser thenK pLit("^") thenS exprParser thenK pLit(")") appl ({ case (e1, e2) => Cat(e1, e2) })
  private val lenParser : Parser[Expr] =
    pLit("|") thenJ exprParser thenK pLit("|") appl (e => Len(e))
  private val letParser : Parser[Expr] = pLit("let") thenJ pIdent thenK pLit("be") thenS exprParser thenK pLit("in") thenS exprParser appl
    ({ case ((n, d), b) => Let(d, n, b) })
  private val apParser : Parser[Expr] =
    pLit("(") thenJ exprParser thenS exprParser thenK pLit(")") appl ({ case (e1, e2) => Ap(e1, e2) })
  private val fundefParser : Parser[Expr] =
    pLit("fun") thenJ pIdent thenK pLit("(") thenS pIdent thenK pLit(":") thenS tyParser thenK pLit(")") thenK pLit("=") thenS
      exprParser thenK pLit("in") thenS exprParser appl ({ case ((((f, x), t), e2), e) => Let(Lam(t, x, e2), f, e) })
  private val lamParser : Parser[Expr] =
    pLit("\\") thenJ pIdent thenK pLit(":") thenS tyParser thenK pLit(".") thenS exprParser appl ({ case ((x, t), e) => Lam(t, x, e) })

  val exprParser : Parser[Expr] =
    varParser or numParser or strParser or plusParser or timesParser or catParser or lenParser or letParser or apParser or fundefParser or lamParser

}