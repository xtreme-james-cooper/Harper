package interpreter

import model.{
  ZPat,
  Z,
  WildPat,
  Voidd,
  VarPat,
  Var,
  Unitt,
  Type,
  TrivPat,
  Triv,
  Sum,
  SPat,
  S,
  ProjR,
  ProjL,
  Prod,
  Pattern,
  Pairr,
  PairPat,
  Nat,
  Match,
  Lam,
  InRPat,
  InR,
  InLPat,
  InL,
  Fix,
  Expr,
  Arr,
  Ap,
  Abort
}
import model.TrivC
import model.Constraint
import model.InL
import model.Triv
import model.All
import model.Triv
import model.InL
import model.ZC
import model.InL
import model.Triv
import model.Z
import model.SC
import model.S
import model.PairC
import model.InL
import model.Triv
import model.InLC
import model.InRC
import model.Z
import model.S
import model.InL
import model.Triv
import model.Z
import model.S
import model.Or
import model.Z
import model.Triv
import model.S
import model.InL

object Typechecker {

  def typecheck : Expr => Type = typecheckExpr(Map())

  private def typecheckExpr(sig : Map[String, Type]) : Expr => Type = {
    case Var(x) => sig.getOrElse(x, throw new Exception("unbound variable " + x))
    case Z      => Nat
    case S(e) =>
      if (typecheckExpr(sig)(e) == Nat) Nat
      else throw new Exception("successor of non-nat " + e)
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
    case Abort(t, e) =>
      if (typecheckExpr(sig)(e) == Voidd) t
      else throw new Exception("abort of non-void " + e)
    case InL(Sum(t1, t2), e) =>
      if (typecheckExpr(sig)(e) == t1) Sum(t1, t2)
      else throw new Exception("inL of incompatible left type " + e)
    case InL(t, e) => throw new Exception("inL to non-sum-type " + t)
    case InR(Sum(t1, t2), e) =>
      if (typecheckExpr(sig)(e) == t2) Sum(t1, t2)
      else throw new Exception("inL of incompatible left type " + e)
    case InR(t, e)    => throw new Exception("inR to non-sum-type " + t)
    case Match(e, rs) => typecheckRules(sig, rs, typecheckExpr(sig)(e))
  }

  private def typecheckRules(sig : Map[String, Type], rs : List[(Pattern, Expr)], t : Type) : Type = {
    val typ = typecheckRule(sig, rs.head, t)
    if (rs.forall(r => typecheckRule(sig, r, t) == typ)) typ
    else throw new Exception("incompatible branches " + rs)
  }

  private def typecheckRule(sig : Map[String, Type], r : (Pattern, Expr), t : Type) : Type = {
    val bind = typecheckPat(r._1, t)
    typecheckExpr(sig ++ bind)(r._2)
  }

  private def typecheckPat : (Pattern, Type) => Map[String, Type] = {
    case (WildPat, _)     => Map()
    case (VarPat(x), t)   => Map(x -> t)
    case (TrivPat, Unitt) => Map()
    case (TrivPat, t)     => throw new Exception("got unit for type " + t)
    case (PairPat(p1, p2), Prod(t1, t2)) => {
      val m1 = typecheckPat(p1, t1)
      val m2 = typecheckPat(p2, t2)
      if (m1.keySet & m2.keySet isEmpty) m1 ++ m2
      else throw new Exception("overlapping variables " + (m1.keySet & m2.keySet))
    }
    case (PairPat(p1, p2), t)     => throw new Exception("got product for type " + t)
    case (InLPat(p), Sum(t1, t2)) => typecheckPat(p, t1)
    case (InLPat(p), t)           => throw new Exception("got sum for type " + t)
    case (InRPat(p), Sum(t1, t2)) => typecheckPat(p, t2)
    case (InRPat(p), t)           => throw new Exception("got sum for type " + t)
    case (ZPat, Nat)              => Map()
    case (ZPat, t)                => throw new Exception("got nat for type " + t)
    case (SPat(p), Nat)           => typecheckPat(p, Nat)
    case (SPat(p), t)             => throw new Exception("got nat for type " + t)
  }

}