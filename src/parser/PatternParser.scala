package parser

import Parser.{ pLit, pIdent }
import ExprParser.exprParser
import model.{ ZPat, WildPat, VarPat, TrivPat, SPat, Rule, Pattern, PairPat, InRPat, InLPat }

object PatternParser {

  private val wildPatParser : Parser[Pattern] = pLit("_") appl (_ => WildPat)
  private val varPatParser : Parser[Pattern] = pIdent appl (s => VarPat(s))
  private val zPatParser : Parser[Pattern] = pLit("Z") appl (_ => ZPat)
  private val sPatParser : Parser[Pattern] = pLit("S") thenJ pLit("(") thenJ patParser thenK pLit(")") appl (e => SPat(e))
  private val trivPatParser : Parser[Pattern] = pLit("(") thenK pLit(")") appl (_ => TrivPat)
  private val pairPatParser : Parser[Pattern] =
    pLit("(") thenJ patParser thenK pLit(",") thenS patParser thenK pLit(")") appl ({ case (t1, t2) => PairPat(t1, t2) })
  private val inlPatParser : Parser[Pattern] = pLit("inl") thenJ patParser appl (e => InLPat(e))
  private val inrPatParser : Parser[Pattern] = pLit("inr") thenJ patParser appl (e => InRPat(e))
  
  private val patParser : Parser[Pattern] =
    wildPatParser or zPatParser or sPatParser or varPatParser or trivPatParser or pairPatParser or inlPatParser or inrPatParser

  private val ruleParser : Parser[Rule] = patParser thenK pLit("-") thenK pLit(">") thenS exprParser appl ({ case (p, e) => new Rule(p, e) })

  val rulesParser : Parser[List[Rule]] = ruleParser thenS (pLit("|") thenJ ruleParser).star appl ({ case (r, rs) => r :: rs })

}