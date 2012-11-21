package parser

import CommandParser.commandParser
import Parser.{ pNum, pLit, pIdent }
import PatternParser.rulesParser
import TypeParser.typeParser
import model.{ Z, Var, Unfold, TypeLam, TypeApp, TryCatch, Triv, ThrowEx, S, PairEx, Match, Lam, InR, InL, Fold, Expr, CommandExp, App }

object ExprParser {

  private val varParser : Parser[Expr] = pIdent appl (s => Var(s))
  private val zParser : Parser[Expr] = pLit("Z") appl (s => Z)
  private val sParser : Parser[Expr] = pLit("S") thenJ pLit("(") thenJ exprParser thenK pLit(")") appl (e => S(e))
  private val numParser : Parser[Expr] = pNum appl (digitToSZ _)
  private def digitToSZ(n : Int) : Expr = if (n == 0) Z else S(digitToSZ(n - 1))
  private val matchParser : Parser[Expr] =
    pLit("case") thenJ exprParser thenK pLit("of") thenK pLit("{") thenS rulesParser thenK pLit("}") appl ({
      case (e, rs) => Match(e, rs)
    })
  private val lamParser : Parser[Expr] =
    pLit("\\") thenJ pIdent thenK pLit(":") thenS typeParser thenK pLit(".") thenS exprParser appl ({
      case ((v, t), e) => Lam(v, t, e)
    })
  private val appParser : Parser[Expr] =
    pLit("(") thenJ exprParser thenS exprParser thenK pLit(")") appl ({ case (e1, e2) => App(e1, e2) })
  private val trivParser : Parser[Expr] = pLit("(") thenK pLit(")") appl (_ => Triv)
  private val pairParser : Parser[Expr] =
    pLit("(") thenJ exprParser thenK pLit(",") thenS exprParser thenK pLit(")") appl ({ case (t1, t2) => PairEx(t1, t2) })
  private val inlParser : Parser[Expr] =
    pLit("inl") thenJ exprParser appl (e => InL(e))
  private val inrParser : Parser[Expr] =
    pLit("inr") thenJ exprParser appl (e => InR(e))
  private val recurseParser : Parser[Expr] = pLit("unfold") thenJ exprParser appl ({ case (e) => Unfold(e) })
  private val foldParser : Parser[Expr] =
    pLit("fold") thenJ pIdent thenK pLit(".") thenS typeParser thenS exprParser appl ({
      case ((mu, t), e) => Fold(mu, t, e)
    })
  private val typeLamParser : Parser[Expr] =
    pLit("/") thenJ pLit("\\") thenJ pIdent thenK pLit(".") thenS exprParser appl ({
      case (t, e) => TypeLam(t, e)
    })
  private val typeAppParser : Parser[Expr] =
    pLit("[") thenJ exprParser thenS typeParser thenK pLit("]") appl ({ case (e, t) => TypeApp(e, t) })
  private val throwParser : Parser[Expr] = pLit("throw") thenJ pIdent appl ({ s => ThrowEx(s) })
  private val catchParser : Parser[Expr] =
    pLit("try") thenJ exprParser thenK pLit("catch") thenS exprParser appl ({ case (e1, e2) => TryCatch(e1, e2) })
  private val cmdExprParser : Parser[Expr] = pLit("command") thenJ commandParser appl (c => CommandExp(c))

  val exprParser : Parser[Expr] =
    zParser or sParser or numParser or matchParser or lamParser or appParser or varParser or
      trivParser or pairParser or inlParser or inrParser or recurseParser or foldParser or typeLamParser or
      typeAppParser or throwParser or catchParser or cmdExprParser

}