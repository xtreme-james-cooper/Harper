package all.parser

import all.model.Expr
import ExprParser.exprParser

object ProgParser {

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
      case (p, x) :: ps   => firstFullParse(ps)
    }

    firstFullParse(exprParser.run(tokenize(s)))
  }

}