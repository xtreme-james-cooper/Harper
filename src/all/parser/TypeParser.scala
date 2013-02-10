package all.parser

import all.Parser
import all.Parser.{ pLit, pIdent }
import all.model.{ Voidd, Unitt, Type, TyVar, Sum, Rec, Prod, Nat, Arr }
import all.model.All

object TypeParser {

  private val natParser : Parser[Type] = pLit("Nat") appl (x => Nat)
  private val arrParser : Parser[Type] = pLit("(") thenJ typeParser thenK pLit("=") thenK pLit(">") thenS typeParser thenK pLit(")") appl
    ({ case (t1, t2) => Arr(t1, t2) })
  private val unitParser : Parser[Type] = pLit("Unit") appl (x => Unitt)
  private val prodParser : Parser[Type] = pLit("(") thenJ typeParser thenK pLit(",") thenS typeParser thenK pLit(")") appl
    ({ case (t1, t2) => Prod(t1, t2) })
  private val voidParser : Parser[Type] = pLit("Void") appl (x => Voidd)
  private val sumParser : Parser[Type] = pLit("(") thenJ typeParser thenK pLit("+") thenS typeParser thenK pLit(")") appl
    ({ case (t1, t2) => Sum(t1, t2) })
  private val tyvarParser : Parser[Type] = pIdent appl (x => TyVar(x))
  private val recParser : Parser[Type] = pLit("mu") thenJ pIdent thenK pLit(".") thenS typeParser appl ({ case (x, t) => Rec(x, t) })
  private val allParser : Parser[Type] = pLit("all") thenJ pIdent thenK pLit(".") thenS typeParser appl ({ case (x, t) => All(x, t) })
  
  val typeParser : Parser[Type] = natParser or arrParser or unitParser or prodParser or voidParser or sumParser or tyvarParser or recParser or allParser

}