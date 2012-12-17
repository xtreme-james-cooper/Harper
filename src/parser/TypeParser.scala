package parser

import Parser.pLit
import model.{ Voidd, Unitt, Type, Sum, Prod, Nat, Arr }

object TypeParser {

  val natParser : Parser[Type] = pLit("Nat") appl (x => Nat)
  val arrParser : Parser[Type] = pLit("(") thenJ typeParser thenK pLit("=") thenK pLit(">") thenS typeParser thenK pLit(")") appl
    ({ case (t1, t2) => Arr(t1, t2) })
  val unitParser : Parser[Type] = pLit("Unit") appl (x => Unitt)
  val prodParser : Parser[Type] = pLit("(") thenJ typeParser thenK pLit(",") thenS typeParser thenK pLit(")") appl
    ({ case (t1, t2) => Prod(t1, t2) })
  val voidParser : Parser[Type] = pLit("Void") appl (x => Voidd)
  val sumParser : Parser[Type] = pLit("(") thenJ typeParser thenK pLit("+") thenS typeParser thenK pLit(")") appl
    ({ case (t1, t2) => Sum(t1, t2) })

  val typeParser : Parser[Type] = natParser or arrParser or unitParser or prodParser or voidParser or sumParser

}