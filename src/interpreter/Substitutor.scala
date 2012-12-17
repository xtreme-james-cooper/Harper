package interpreter

import model.{ Z, Var, Triv, S, ProjR, ProjL, Pairr, Lam, IfZ, Fix, Expr, Ap }
import model.Abort
import model.InR
import model.InL
import model.Case

object Substitutor {

  private var varTag : Int = 0

  private def newVar : String = {
    varTag = varTag + 1
    "var-" + varTag
  }

  def subst(x : String, v : Expr) : Expr => Expr = {
    case Var(y) =>
      if (x == y) v
      else Var(y)
    case Z    => Z
    case S(n) => S(subst(x, v)(n))
    case IfZ(e, ez, y, es) =>
      if (x == y) IfZ(subst(x, v)(e), subst(x, v)(ez), y, es)
      else {
        val newV : String = newVar
        IfZ(subst(x, v)(e), subst(x, v)(ez), newV, subst(x, v)(subst(y, Var(newV))(es)))
      }
    case Lam(y, t, e) => {
      val newV : String = newVar
      Lam(newV, t, subst(x, v)(subst(y, Var(newV))(e)))
    }
    case Ap(e1, e2) => Ap(subst(x, v)(e1), subst(x, v)(e2))
    case Fix(y, t, e) => {
      val newV : String = newVar
      Fix(newV, t, subst(x, v)(subst(y, Var(newV))(e)))
    }
    case Triv          => Triv
    case Pairr(e1, e2) => Pairr(subst(x, v)(e1), subst(x, v)(e2))
    case ProjL(e)      => ProjL(subst(x, v)(e))
    case ProjR(e)      => ProjR(subst(x, v)(e))
    case Abort(t, e)   => Abort(t, subst(x, v)(e))
    case InL(t, e)     => InL(t, subst(x, v)(e))
    case InR(t, e)     => InR(t, subst(x, v)(e))
    case Case(e, y1, e1, y2, e2) =>
      if (x == y1) 
        if (x == y2) Case(subst(x, v)(e), y1, e1, y2, e2)
        else {
          val newV : String = newVar
          Case(subst(x, v)(e), y1, e1, newV, subst(x, v)(subst(y2, Var(newV))(e2)))
        }
      else if (x == y2) {
        val newV : String = newVar
          Case(subst(x, v)(e), newV, subst(x, v)(subst(y1, Var(newV))(e1)), y2, e2)
      } else {
        val newV1 : String = newVar
        val newV2 : String = newVar
        Case(subst(x, v)(e), newV1, subst(x, v)(subst(y1, Var(newV1))(e1)), newV2, subst(x, v)(subst(y2, Var(newV2))(e2)))
      }

  }

}