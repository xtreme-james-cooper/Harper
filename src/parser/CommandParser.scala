package parser

import ExprParser.exprParser
import Parser.{ pLit, pIdent }
import model.{ SetCmd, Ret, Get, Decl, Command, Bind }

object CommandParser {

  private val returnParser : Parser[Command] = pLit("return") thenJ exprParser appl (e => Ret(e))
  private val bindParser : Parser[Command] =
    pLit("bind") thenJ pIdent thenK pLit("<") thenK pLit("-") thenS exprParser thenK pLit(";") thenS commandParser appl ({
      case ((x, e), m) => Bind(x, e, m)
    })
  private val declParser : Parser[Command] =
    pLit("decl") thenJ pIdent thenK pLit(":") thenK pLit("=") thenS exprParser thenK pLit("in") thenS commandParser appl ({
      case ((x, e), m) => Decl(x, e, m)
    })
  private val getParser : Parser[Command] = pLit("!") thenJ pIdent appl (x => Get(x))
  private val setParser : Parser[Command] =
    pIdent thenK pLit(":") thenK pLit("=") thenS exprParser thenK pLit(";") thenS commandParser appl ({
      case ((x, e), m) => SetCmd(x, e, m)
    })
  
  val commandParser : Parser[Command] = returnParser or bindParser or declParser or getParser or setParser

}