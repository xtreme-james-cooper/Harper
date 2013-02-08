package parser

import Parser.{ pLit, pIdent }
import PatParser.rulesParser
import TypeParser.typeParser
import model.{ Z, Var, Unfold, Triv, TLam, TAp, S, Raise, ProjR, ProjL, Pairr, Match, Let, Lam, InR, InL, Fold, Fix, Expr, Ap, Abort }
import model.Catch

object ExprParser {

  private val varParser : Parser[Expr] = pIdent appl (x => Var(x))
  private val zParser : Parser[Expr] = pLit("Z") appl (s => Z)
  private val sParser : Parser[Expr] = pLit("S") thenJ pLit("(") thenJ exprParser thenK pLit(")") appl (e => S(e))
  private val lamParser : Parser[Expr] =
    pLit("\\") thenJ pIdent thenK pLit(":") thenS typeParser thenK pLit(".") thenS exprParser appl ({ case ((x, t), e) => Lam(x, t, e) })
  private val apParser : Parser[Expr] =
    pLit("(") thenJ exprParser thenS exprParser thenK pLit(")") appl ({ case (e1, e2) => Ap(e1, e2) })
  private val fixParser : Parser[Expr] =
    pLit("fix") thenJ pIdent thenK pLit(":") thenS typeParser thenK pLit("in") thenS exprParser appl ({ case ((x, t), e) => Fix(x, t, e) })
  private val trivParser : Parser[Expr] = pLit("(") thenK pLit(")") appl (x => Triv)
  private val pairParser : Parser[Expr] = pLit("(") thenJ exprParser thenK pLit(",") thenS exprParser thenK pLit(")") appl
    ({ case (t1, t2) => Pairr(t1, t2) })
  private val projLParser : Parser[Expr] = pLit("projL") thenJ exprParser appl (x => ProjL(x))
  private val projRParser : Parser[Expr] = pLit("projR") thenJ exprParser appl (x => ProjR(x))
  private val abortParser : Parser[Expr] = pLit("abort") thenJ pLit(":") thenJ typeParser thenS exprParser appl ({ case (t, e) => Abort(t, e) })
  private val inLParser : Parser[Expr] = pLit("inL") thenJ pLit(":") thenJ typeParser thenS exprParser appl ({ case (t, e) => InL(t, e) })
  private val inRParser : Parser[Expr] = pLit("inR") thenJ pLit(":") thenJ typeParser thenS exprParser appl ({ case (t, e) => InR(t, e) })
  private val matchParser : Parser[Expr] =
    pLit("case") thenJ exprParser thenK pLit("of") thenK pLit("{") thenS rulesParser thenK pLit("}") appl
      ({ case (e, rs) => Match(e, rs) })
  private val foldParser : Parser[Expr] = pLit("fold") thenJ pLit(":") thenJ pIdent thenK pLit(".") thenS typeParser thenS exprParser appl
    ({ case ((x, t), e) => Fold(x, t, e) })
  private val unfoldParser : Parser[Expr] = pLit("unfold") thenJ exprParser appl (e => Unfold(e))
  private val letParser : Parser[Expr] = pLit("let") thenJ pIdent thenK pLit("=") thenS exprParser thenK pLit("in") thenS exprParser appl
    ({ case ((n, d), b) => Let(n, d, b) })
  private val tlamParser : Parser[Expr] =
    pLit("/") thenJ pLit("\\") thenJ pIdent thenK pLit(".") thenS exprParser appl ({ case (x, e) => TLam(x, e) })
  private val tapParser : Parser[Expr] =
    pLit("[") thenJ exprParser thenS typeParser thenK pLit("]") appl ({ case (e, t) => TAp(e, t) })
  private val raiseParser : Parser[Expr] =
    pLit("raise") thenJ pLit(":") thenJ typeParser appl ({ case t => Raise(t) })
  private val catchParser : Parser[Expr] =
    pLit("try") thenJ exprParser thenK pLit("catch") thenS exprParser appl ({ case (e1, e2) => Catch(e1, e2) })

  val exprParser : Parser[Expr] =
    varParser or zParser or sParser or lamParser or apParser or fixParser or trivParser or pairParser or projLParser or projRParser or
      abortParser or inLParser or inRParser or matchParser or foldParser or unfoldParser or letParser or tlamParser or tapParser or
      raiseParser or catchParser

}