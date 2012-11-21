package parser

import CommandParser.commandParser
import ExprParser.exprParser
import Parser.{ pUpperIdent, pLit, pIdent, pEnd, pEmpty }
import TypeParser.typeParser
import model.{ TypeDefn, Type, Prog, ExprDefn, Defn, CommandTy, CommandExp }

object ProgParser {

  private def tokenize(s : String) : List[String] = s.headOption match {
    case None                      => Nil
    case Some(c) if c.isWhitespace => tokenize(s.tail)
    case Some(c) if c.isDigit      => s.takeWhile(_ isDigit) :: tokenize(s.dropWhile(_ isDigit))
    case Some(c) if c.isLetter     => s.takeWhile(_ isLetterOrDigit) :: tokenize(s.dropWhile(_ isLetterOrDigit))
    case Some(c)                   => c.toString :: tokenize(s.tail)
  }

  private val paramListParser : Parser[List[(String, Type)]] =
    (pLit("(") thenJ (pIdent thenK pLit(":") thenS typeParser).intersperse(pLit(",")) thenK pLit(")")) or
      (pEmpty appl (_ => Nil))
  private val nameParser : Parser[((String, List[(String, Type)]), Type)] = pIdent thenS paramListParser thenK pLit(":") thenS typeParser
  private val exprDefnParser : Parser[Defn] =
    nameParser thenK pLit("=") thenS exprParser thenK pLit(";") appl ({ case (((n, args), t), e) => new ExprDefn(n, args, t, e) })
  private val typeDefnParser : Parser[Defn] =
    pLit("type") thenJ pUpperIdent thenK pLit("=") thenS typeParser thenK pLit(";") appl ({ case (n, t) => TypeDefn(n, t) })
  private val procDefnParser : Parser[Defn] =
    nameParser thenK pLit("=") thenS commandParser thenK pLit(";") appl ({ case (((n, args), t), c) => new ExprDefn(n, args, CommandTy(t), CommandExp(c)) })
  private val defnParser : Parser[Defn] = exprDefnParser or typeDefnParser or procDefnParser

  private val progParser : Parser[Prog] = defnParser.star thenS commandParser thenK pEnd appl ({
    case (defs, e) => new Prog(defs, e)
  })

  def parse(s : String) : Prog = progParser.run(tokenize(s)).head._1

}