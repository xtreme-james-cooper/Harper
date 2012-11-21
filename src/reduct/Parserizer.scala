package reduct

import src.Parser
import src.Parser.pLit
import src.Parser.pEnd
import src.Parser.pIdent
import src.Parser.pUpperIdent
import src.Parser.pLit
import src.Parser.pEmpty
import src.Parser.pNum
import model.Expr
import model.Type
import model.Var
import model.Prog
import model.Defn
import model.ExprDefn
import model.Fix
import model.S
import model.Z
import model.Nat
import model.Arrow
import model.UnitTy
import model.Product
import model.App
import model.Lam
import model.Triv
import model.PairEx
import model.Sum
import model.InR
import model.InL
import model.Match
import model.Rule
import model.WildPat
import model.Pattern
import model.VarPat
import model.ZPat
import model.SPat
import model.TrivPat
import model.PairPat
import model.InLPat
import model.InRPat
import model.TyVar
import model.Inductive
import model.Unfold
import model.Fold
import model.ForAll
import model.TypeLam
import model.TypeApp
import model.TypeDefn
import model.ThrowEx
import model.TryCatch

object Parserizer {

  def tokenize(s : String) : List[String] = s.headOption match {
    case None                      => Nil
    case Some(c) if c.isWhitespace => tokenize(s.tail)
    case Some(c) if c.isDigit      => s.takeWhile(_ isDigit) :: tokenize(s.dropWhile(_ isDigit))
    case Some(c) if c.isLetter     => s.takeWhile(_ isLetterOrDigit) :: tokenize(s.dropWhile(_ isLetterOrDigit))
    case Some(c)                   => c.toString :: tokenize(s.tail)
  }

  val arrowParser : Parser[Type] =
    pLit("(") thenJ typeParser thenK pLit("-") thenK pLit(">") thenS typeParser thenK pLit(")") appl ({ case (t1, t2) => Arrow(t1, t2) })
  val productParser : Parser[Type] =
    pLit("(") thenJ typeParser thenK pLit(",") thenS typeParser thenK pLit(")") appl ({ case (t1, t2) => Product(t1, t2) })
  val sumParser : Parser[Type] =
    pLit("(") thenJ typeParser thenK pLit("+") thenS typeParser thenK pLit(")") appl ({ case (t1, t2) => Sum(t1, t2) })
  val inductiveParser : Parser[Type] = pLit("mu") thenJ pIdent thenK pLit(".") thenS typeParser appl ({ case (x, t) => Inductive(x, t) })
  val forallParser : Parser[Type] = pLit("forall") thenJ pIdent thenK pLit(".") thenS typeParser appl ({ case (x, t) => ForAll(x, t) })
  val varTyParser : Parser[Type] = pIdent appl (x => TyVar(x))
  val synonymParser : Parser[Type] = pUpperIdent appl (x => TyVar(x)) //separate so if we ever want to distinguish TyVars and TySynonyms
  val typeParser : Parser[Type] =
    arrowParser or productParser or sumParser or inductiveParser or forallParser or varTyParser or synonymParser

  val wildPatParser : Parser[Pattern] = pLit("_") appl (_ => WildPat)
  val varPatParser : Parser[Pattern] = pIdent appl (s => VarPat(s))
  val zPatParser : Parser[Pattern] = pLit("Z") appl (_ => ZPat)
  val sPatParser : Parser[Pattern] = pLit("S") thenJ pLit("(") thenJ patParser thenK pLit(")") appl (e => SPat(e))
  val trivPatParser : Parser[Pattern] = pLit("(") thenK pLit(")") appl (_ => TrivPat)
  val pairPatParser : Parser[Pattern] =
    pLit("(") thenJ patParser thenK pLit(",") thenS patParser thenK pLit(")") appl ({ case (t1, t2) => PairPat(t1, t2) })
  val inlPatParser : Parser[Pattern] = pLit("inl") thenJ patParser appl (e => InLPat(e))
  val inrPatParser : Parser[Pattern] = pLit("inr") thenJ patParser appl (e => InRPat(e))
  val patParser : Parser[Pattern] =
    wildPatParser or zPatParser or sPatParser or varPatParser or trivPatParser or pairPatParser or inlPatParser or inrPatParser

  val ruleParser : Parser[Rule] = patParser thenK pLit("-") thenK pLit(">") thenS exprParser appl ({ case (p, e) => new Rule(p, e) })

  val rulesParser : Parser[List[Rule]] = ruleParser thenS (pLit("|") thenJ ruleParser).star appl ({ case (r, rs) => r :: rs })

  val varParser : Parser[Expr] = pIdent appl (s => Var(s))
  val zParser : Parser[Expr] = pLit("Z") appl (s => Z)
  val sParser : Parser[Expr] = pLit("S") thenJ pLit("(") thenJ exprParser thenK pLit(")") appl (e => S(e))
  val numParser : Parser[Expr] = pNum appl (digitToSZ _)
  def digitToSZ(n : Int) : Expr = if (n == 0) Z else S(digitToSZ(n - 1))
  val matchParser : Parser[Expr] =
    pLit("case") thenJ exprParser thenK pLit("of") thenK pLit("{") thenS rulesParser thenK pLit("}") appl ({
      case (e, rs) => Match(e, rs)
    })
  val lamParser : Parser[Expr] =
    pLit("\\") thenJ pIdent thenK pLit(":") thenS typeParser thenK pLit(".") thenS exprParser appl ({
      case ((v, t), e) => Lam(v, t, e)
    })
  val appParser : Parser[Expr] =
    pLit("(") thenJ exprParser thenS exprParser thenK pLit(")") appl ({ case (e1, e2) => App(e1, e2) })
  val trivParser : Parser[Expr] = pLit("(") thenK pLit(")") appl (_ => Triv)
  val pairParser : Parser[Expr] =
    pLit("(") thenJ exprParser thenK pLit(",") thenS exprParser thenK pLit(")") appl ({ case (t1, t2) => PairEx(t1, t2) })
  val inlParser : Parser[Expr] =
    pLit("inl") thenJ exprParser appl (e => InL(e))
  val inrParser : Parser[Expr] =
    pLit("inr") thenJ exprParser appl (e => InR(e))
  val recurseParser : Parser[Expr] = pLit("unfold") thenJ exprParser appl ({ case (e) => Unfold(e) })
  val foldParser : Parser[Expr] =
    pLit("fold") thenJ pIdent thenK pLit(".") thenS typeParser thenS exprParser appl ({
      case ((mu, t), e) => Fold(mu, t, e)
    })
  val typeLamParser : Parser[Expr] =
    pLit("/") thenJ pLit("\\") thenJ pIdent thenK pLit(".") thenS exprParser appl ({
      case (t, e) => TypeLam(t, e)
    })
  val typeAppParser : Parser[Expr] =
    pLit("[") thenJ exprParser thenS typeParser thenK pLit("]") appl ({ case (e, t) => TypeApp(e, t) })
  val throwParser : Parser[Expr] = pLit("throw") thenJ pIdent appl ({ s => ThrowEx(s) })
  val catchParser : Parser[Expr] =
    pLit("try") thenJ exprParser thenK pLit("catch") thenS exprParser appl ({ case (e1, e2) => TryCatch(e1, e2) })
  val exprParser : Parser[Expr] =
    zParser or sParser or numParser or matchParser or lamParser or appParser or varParser or
      trivParser or pairParser or inlParser or inrParser or recurseParser or foldParser or typeLamParser or
      typeAppParser or throwParser or catchParser

  val paramListParser : Parser[List[(String, Type)]] =
    (pLit("(") thenJ (pIdent thenK pLit(":") thenS typeParser).intersperse(pLit(",")) thenK pLit(")")) or
      (pEmpty appl (_ => Nil))
  val nameParser : Parser[((String, List[(String, Type)]), Type)] = pIdent thenS paramListParser thenK pLit(":") thenS typeParser
  val exprDefnParser : Parser[Defn] =
    nameParser thenK pLit("=") thenS exprParser thenK pLit(";") appl ({ case (((n, args), t), e) => new ExprDefn(n, args, t, e) })
  val typeDefnParser : Parser[Defn] =
    pLit("type") thenJ pUpperIdent thenK pLit("=") thenS typeParser thenK pLit(";") appl ({ case (n, t) => TypeDefn(n, t) })
  val defnParser : Parser[Defn] = exprDefnParser or typeDefnParser

  val progParser : Parser[Prog] = defnParser.star thenS exprParser thenK pEnd appl ({
    case (defs, e) => new Prog(builtinDefs ++ defs, e)
  })

  def parse(s : String) : Prog = progParser.run(tokenize(s)).head._1

  val builtinDefs : List[Defn] = List(
    TypeDefn("Unit", UnitTy), TypeDefn("Nat", Nat), TypeDefn("Bool", Sum(UnitTy, UnitTy)), new ExprDefn("true", Nil, TyVar("Bool"), InL(Triv)),
    new ExprDefn("false", Nil, TyVar("Bool"), InR(Triv)))

}