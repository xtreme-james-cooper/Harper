package parser

import Parser.{ pLit, pIdent }
import TypeParser.typeParser
import model.{ Z, Var, S, Lam, IfZ, Fix, Expr, Ap }

object ExprParser {

  private val varParser : Parser[Expr] = pIdent appl (x => Var(x))
  private val zParser : Parser[Expr] = pLit("Z") appl (s => Z)
  private val sParser : Parser[Expr] = pLit("S") thenJ pLit("(") thenJ exprParser thenK pLit(")") appl (e => S(e))
  private val ifzParser : Parser[Expr] =
    pLit("ifz") thenJ exprParser thenK pLit("{") thenK pLit("Z") thenK pLit("=") thenK pLit(">") thenS exprParser thenK pLit(";") thenK
      pLit("S") thenK pLit("(") thenS pIdent thenK pLit(")") thenK pLit("=") thenK pLit(">") thenS exprParser thenK pLit("}") appl
      ({ case (((e, ez), x), es) => IfZ(e, ez, x, es) })
  private val lamParser : Parser[Expr] =
    pLit("\\") thenJ pIdent thenK pLit(":") thenS typeParser thenK pLit(".") thenS exprParser appl ({ case ((x, t), e) => Lam(x, t, e) })
  private val apParser : Parser[Expr] =
    pLit("(") thenJ exprParser thenS exprParser thenK pLit(")") appl ({ case (e1, e2) => Ap(e1, e2) })
  private val fixParser : Parser[Expr] =
    pLit("fix") thenJ pIdent thenK pLit(":") thenS typeParser thenK pLit("in") thenS exprParser appl ({ case ((x, t), e) => Fix(x, t, e) })

  val exprParser : Parser[Expr] =
    varParser or zParser or sParser or ifzParser or lamParser or apParser or fixParser

}