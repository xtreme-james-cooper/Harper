package interpreter

import model.{ Z, Var, S, IfZ, Expr }

object Substitutor {

  var varTag : Int = 0

  def newVar : String = {
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
  }

}