package interpreter

import model.{ Z, Var, S, Lam, IfZ, Fix, Expr, Ap }
import model.Value

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
  }

}