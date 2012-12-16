package interpreter

import model.{ Z, Type, S, Nat, Expr, Var, IfZ }

object Typechecker {

  private def typecheckExpr(sig : Map[String, Type]) : Expr => Type = {
    case Var(x) => sig.getOrElse(x, throw new Exception("unbound variable " + x))
    case Z => Nat
    case S(e) =>
      if (typecheckExpr(sig)(e) == Nat) Nat
      else throw new Exception("successor of non-nat " + e)
    case IfZ(e, ez, x, es) =>
      if (typecheckExpr(sig)(e) == Nat) {
        val t = typecheckExpr(sig)(ez)
        if (typecheckExpr(sig + (x -> Nat))(es) == t) t
        else throw new Exception("incompatible ifz branches " + ez + " and " + es)
      } else throw new Exception("ifz of non-nat " + e)
  }

  def typecheck : Expr => Type = typecheckExpr(Map())
  
}