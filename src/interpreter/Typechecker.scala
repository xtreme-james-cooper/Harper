package interpreter

import model.Expr
import model.{ Z, Var, Unitt, Type, Triv, S, ProjR, ProjL, Prod, Pairr, Nat, Lam, IfZ, Fix, Arr, Ap }

object Typechecker {

  private def typecheckExpr(sig : Map[String, Type]) : Expr => Type = {
    case Var(x) => sig.getOrElse(x, throw new Exception("unbound variable " + x))
    case Z      => Nat
    case S(e) =>
      if (typecheckExpr(sig)(e) == Nat) Nat
      else throw new Exception("successor of non-nat " + e)
    case IfZ(e, ez, x, es) =>
      if (typecheckExpr(sig)(e) == Nat) {
        val t = typecheckExpr(sig)(ez)
        if (typecheckExpr(sig + (x -> Nat))(es) == t) t
        else throw new Exception("incompatible ifz branches " + ez + " and " + es)
      } else throw new Exception("ifz of non-nat " + e)
    case Lam(x, t, e) => Arr(t, typecheckExpr(sig + (x -> t))(e))
    case Ap(e1, e2) => typecheckExpr(sig)(e1) match {
      case Arr(t1, t2) =>
        if (typecheckExpr(sig)(e2) == t1) t2
        else throw new Exception("application of wrong argument type " + e2)
      case _ => throw new Exception("application of non-function " + e1)
    }
    case Fix(x, t, e) =>
      if (typecheckExpr(sig + (x -> t))(e) == t) t
      else throw new Exception("recursive expression does not have declared type " + e)
    case Triv          => Unitt
    case Pairr(e1, e2) => Prod(typecheckExpr(sig)(e1), typecheckExpr(sig)(e2))
    case ProjL(e) => typecheckExpr(sig)(e) match {
      case Prod(t1, t2) => t1
      case _            => throw new Exception("projL of non-product " + e)
    }
    case ProjR(e) => typecheckExpr(sig)(e) match {
      case Prod(t1, t2) => t2
      case _            => throw new Exception("projR of non-product " + e)
    }

  }

  def typecheck : Expr => Type = typecheckExpr(Map())

}