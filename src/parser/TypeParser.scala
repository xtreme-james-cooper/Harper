package parser

import Parser.{ pUpperIdent, pLit, pIdent }
import model.{ Type, TyVar, Sum, Product, Inductive, ForAll, Arrow }

object TypeParser {

  private val arrowParser : Parser[Type] =
    pLit("(") thenJ typeParser thenK pLit("-") thenK pLit(">") thenS typeParser thenK pLit(")") appl ({ case (t1, t2) => Arrow(t1, t2) })
  private val productParser : Parser[Type] =
    pLit("(") thenJ typeParser thenK pLit(",") thenS typeParser thenK pLit(")") appl ({ case (t1, t2) => Product(t1, t2) })
  private val sumParser : Parser[Type] =
    pLit("(") thenJ typeParser thenK pLit("+") thenS typeParser thenK pLit(")") appl ({ case (t1, t2) => Sum(t1, t2) })
  private val inductiveParser : Parser[Type] = pLit("mu") thenJ pIdent thenK pLit(".") thenS typeParser appl ({ case (x, t) => Inductive(x, t) })
  private val forallParser : Parser[Type] = pLit("forall") thenJ pIdent thenK pLit(".") thenS typeParser appl ({ case (x, t) => ForAll(x, t) })
  private val varTyParser : Parser[Type] = pIdent appl (x => TyVar(x))
  private val synonymParser : Parser[Type] = pUpperIdent appl (x => TyVar(x)) //separate so if we ever want to distinguish TyVars and TySynonyms
 
  val typeParser : Parser[Type] =
    arrowParser or productParser or sumParser or inductiveParser or forallParser or varTyParser or synonymParser

}