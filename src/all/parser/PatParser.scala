package all.parser

import all.Parser
import ExprParser.exprParser
import all.Parser.{ pLit, pIdent }
import all.model.{ ZPat, WildPat, VarPat, TrivPat, SPat, Pattern, PairPat, InRPat, InLPat, Expr }

object PatParser {

  private val wildParser : Parser[Pattern] = pLit("_") appl (x => WildPat)
  private val varParser : Parser[Pattern] = pIdent appl (x => VarPat(x))
  private val zParser : Parser[Pattern] = pLit("Z") appl (s => ZPat)
  private val sParser : Parser[Pattern] = pLit("S") thenJ pLit("(") thenJ patternParser thenK pLit(")") appl (e => SPat(e))
  private val trivParser : Parser[Pattern] = pLit("(") thenK pLit(")") appl (x => TrivPat)
  private val pairParser : Parser[Pattern] = pLit("(") thenJ patternParser thenK pLit(",") thenS patternParser thenK pLit(")") appl
    ({ case (t1, t2) => PairPat(t1, t2) })
  private val inLParser : Parser[Pattern] = pLit("inL") thenJ patternParser appl (e => InLPat(e))
  private val inRParser : Parser[Pattern] = pLit("inR") thenJ patternParser appl (e => InRPat(e))

  private val patternParser : Parser[Pattern] =
    wildParser or varParser or zParser or sParser or trivParser or pairParser or inLParser or inRParser

  private val ruleParser : Parser[(Pattern, Expr)] = patternParser thenK pLit("=") thenK pLit(">") thenS exprParser
  
  val rulesParser : Parser[List[(Pattern, Expr)]] = ruleParser intersperse pLit(";")

}