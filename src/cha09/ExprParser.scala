package cha09

import main.Parser
import main.Parser.{ pLit, pIdent, pNum }

object ExprParser {

  private val numTyParser : Parser[Type] = pLit("Num") appl (_ => NumTy)
  private val arrTyParser : Parser[Type] = pLit("(") thenJ tyParser thenK pLit("-") thenK pLit(">") thenS tyParser thenK pLit(")") appl
    ({ case (t1, t2) => ArrTy(t1, t2) })

  private val tyParser : Parser[Type] = numTyParser or arrTyParser

  private val varParser : Parser[Expr] = pIdent appl (x => Var(x))
  private val numParser : Parser[Expr] = pNum appl (n => (0 until n).foldLeft(Z:Expr)((k, _) => S(k)))
  private val sParser : Parser[Expr] = pLit("S") thenJ pLit("(") thenJ exprParser thenK pLit(")") appl (e => S(e))
  private val letParser : Parser[Expr] = pLit("let") thenJ pIdent thenK pLit("be") thenS exprParser thenK pLit("in") thenS exprParser appl
    ({ case ((n, d), b) => Let(d, n, b) })
  private val apParser : Parser[Expr] =
    pLit("(") thenJ exprParser thenS exprParser thenK pLit(")") appl ({ case (e1, e2) => Ap(e1, e2) })
  private val fundefParser : Parser[Expr] =
    pLit("fun") thenJ pIdent thenK pLit("(") thenS pIdent thenK pLit(":") thenS tyParser thenK pLit(")") thenK pLit("=") thenS
      exprParser thenK pLit("in") thenS exprParser appl ({ case ((((f, x), t), e2), e) => Let(Lam(t, x, e2), f, e) })
  private val lamParser : Parser[Expr] =
    pLit("\\") thenJ pIdent thenK pLit(":") thenS tyParser thenK pLit(".") thenS exprParser appl ({ case ((x, t), e) => Lam(t, x, e) })
  private val recParser : Parser[Expr] = 
    pLit("rec") thenJ exprParser thenK pLit("{") thenK pLit("0") thenK pLit("=") thenK pLit(">") thenS exprParser thenK pLit("|") thenK
    pLit("S") thenK pLit("(") thenS pIdent thenK pLit(")") thenK pLit("with") thenS pIdent thenK pLit("=") thenK pLit(">") thenS exprParser thenK
    pLit("}") appl ({ case ((((e, e0), x), y), e1) => Rec(e0, x, y, e1, e) })
  
  val exprParser : Parser[Expr] =
    varParser or numParser or sParser or letParser or apParser or fundefParser or lamParser or recParser

}