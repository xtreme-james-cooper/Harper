package cha07

import all.Parser
import all.Parser.{ pLit, pIdent, pNum }

object ExprParser {

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

  val exprParser : Parser[Expr] =
    varParser or numParser or strParser or plusParser or timesParser or catParser or lenParser or letParser

}