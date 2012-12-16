package parser

import Parser.{ pLit, pIdent }
import model.{ Z, S, Expr, Var, IfZ }

object ExprParser {

  private val varParser : Parser[Expr] = pIdent appl (x => Var(x))
  private val zParser : Parser[Expr] = pLit("Z") appl (s => Z)
  private val sParser : Parser[Expr] = pLit("S") thenJ pLit("(") thenJ exprParser thenK pLit(")") appl (e => S(e))
  private val ifzParser : Parser[Expr] =
    pLit("ifz") thenJ exprParser thenK pLit("{") thenK pLit("Z") thenK pLit("=") thenK pLit(">") thenS exprParser thenK pLit(";") thenK
      pLit("S") thenK pLit("(") thenS pIdent thenK pLit(")") thenK pLit("=") thenK pLit(">") thenS exprParser thenK pLit("}") appl
      ({ case (((e, ez), x), es) => IfZ(e, ez, x, es) })

  val exprParser : Parser[Expr] =
    zParser or sParser or ifzParser or varParser

  def parse(s : String) : Expr = {

    def tokenize(s : String) : List[String] = s.headOption match {
      case None                      => Nil
      case Some(c) if c.isWhitespace => tokenize(s.tail)
      case Some(c) if c.isDigit      => s.takeWhile(_ isDigit) :: tokenize(s.dropWhile(_ isDigit))
      case Some(c) if c.isLetter     => s.takeWhile(_ isLetterOrDigit) :: tokenize(s.dropWhile(_ isLetterOrDigit))
      case Some(c)                   => c.toString :: tokenize(s.tail)
    }

    def firstFullParse(ps : List[(Expr, List[String])]) : Expr = ps match {
      case Nil            => throw new Exception("no full parse of " + s)
      case (p, Nil) :: ps => p
      case (p, x) :: ps => firstFullParse(ps)
    }

    firstFullParse(exprParser.run(tokenize(s)))
  }

}