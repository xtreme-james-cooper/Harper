package cha12

import main.Parser
import main.Parser.{ pLit, pIdent, pNum }

object ExprParser {

  private val numTyParser : Parser[Type] = pLit("Num") appl (_ => NumTy)
  private val arrTyParser : Parser[Type] =
    pLit("(") thenJ tyParser thenK pLit("-") thenK pLit(">") thenS tyParser thenK pLit(")") appl ({ case (t1, t2) => ArrTy(t1, t2) })
  private val prodParser : Parser[Type] =
    pLit("(") thenJ tyParser thenK pLit(",") thenS tyParser thenK pLit(")") appl ({ case (t1, t2) => ProdTy(t1, t2) })
  private val unitParser : Parser[Type] = pLit("Unit") appl (_ => UnitTy)
  private val voidParser : Parser[Type] = pLit("Void") appl (_ => VoidTy)
  private val sumParser : Parser[Type] =
    pLit("(") thenJ tyParser thenK pLit("+") thenS tyParser thenK pLit(")") appl ({ case (t1, t2) => SumTy(t1, t2) })
    
  private val tyParser : Parser[Type] = numTyParser or arrTyParser or prodParser or unitParser or sumParser or voidParser

  private val varParser : Parser[Expr] = pIdent appl (x => Var(x))
  private val numParser : Parser[Expr] = pNum appl (n => (0 until n).foldLeft(Z : Expr)((k, _) => S(k)))
  private val sParser : Parser[Expr] = pLit("S") thenJ pLit("(") thenJ exprParser thenK pLit(")") appl (e => S(e))
  private val letParser : Parser[Expr] = pLit("let") thenJ pIdent thenK pLit("be") thenS exprParser thenK pLit("in") thenS exprParser appl
    ({ case ((n, d), b) => Let(d, n, b) })
  private val apParser : Parser[Expr] =
    pLit("(") thenJ exprParser thenS exprParser thenK pLit(")") appl ({ case (e1, e2) => Ap(e1, e2) })
  private val fundefParser : Parser[Expr] =
    pLit("fun") thenJ pIdent thenK pLit("(") thenS pIdent thenK pLit(":") thenS tyParser thenK pLit(")") thenK pLit(":") thenS tyParser thenK pLit("=") thenS
      exprParser thenK pLit("in") thenS exprParser appl ({ case (((((f, x), t1), t2), e2), e) => Let(Fix(ArrTy(t1, t2), f, (Lam(t1, x, e2))), f, e) })
  private val lamParser : Parser[Expr] =
    pLit("\\") thenJ pIdent thenK pLit(":") thenS tyParser thenK pLit(".") thenS exprParser appl ({ case ((x, t), e) => Lam(t, x, e) })
  private val ifzParser : Parser[Expr] =
    pLit("ifz") thenJ exprParser thenK pLit("{") thenK pLit("0") thenK pLit("=") thenK pLit(">") thenS exprParser thenK pLit("|") thenK
      pLit("S") thenK pLit("(") thenS pIdent thenK pLit(")") thenK pLit("=") thenK pLit(">") thenS exprParser thenK
      pLit("}") appl ({ case (((e, e0), x), e1) => IfZ(e, e0, x, e1) })
  private val fixParser : Parser[Expr] =
    pLit("fix") thenJ pIdent thenK pLit(":") thenS tyParser thenK pLit("is") thenS exprParser appl ({ case ((x, t), e) => Fix(t, x, e) })
  private val pairParser : Parser[Expr] =
    pLit("(") thenJ exprParser thenK pLit(",") thenS exprParser thenK pLit(")") appl ({ case (e1, e2) => Pair(e1, e2) })
  private val prlParser : Parser[Expr] = pLit("projl") thenJ exprParser appl (e => PrL(e))
  private val prrParser : Parser[Expr] = pLit("projr") thenJ exprParser appl (e => PrR(e))
  private val trivParser : Parser[Expr] = pLit("(") thenJ pLit(")") appl (_ => Triv)
  private val abortParser : Parser[Expr] =
    pLit("abort") thenJ pLit(":") thenJ tyParser thenK pLit("(") thenS exprParser thenK pLit(")") appl ({ case (t, e) => Abort(t, e) })
  private val inlParser : Parser[Expr] =
    pLit("inl") thenJ pLit(":") thenJ tyParser thenK pLit("(") thenS exprParser thenK pLit(")") appl ({ case (t, e) => InL(t, e) })
  private val inrParser : Parser[Expr] =
    pLit("inr") thenJ pLit(":") thenJ tyParser thenK pLit("(") thenS exprParser thenK pLit(")") appl ({ case (t, e) => InR(t, e) })
  private val caseParser : Parser[Expr] =
    pLit("case") thenJ exprParser thenK pLit("{") thenK pLit("inl") thenK pLit("(") thenS pIdent thenK pLit (")") thenK pLit("=") thenK pLit(">") thenS
      exprParser thenK pLit("|") thenK pLit("inr") thenK pLit("(") thenS pIdent thenK pLit(")") thenK pLit("=") thenK pLit(">") thenS exprParser thenK
      pLit("}") appl ({ case ((((e, x), e0), y), e1) => Case(e, x, e0, y, e1) })

  val exprParser : Parser[Expr] =
    varParser or numParser or sParser or letParser or apParser or fundefParser or lamParser or ifzParser or fixParser or pairParser or
      prlParser or prrParser or trivParser or abortParser or inlParser or inrParser or caseParser

}