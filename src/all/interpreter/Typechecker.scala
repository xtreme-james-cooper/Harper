package all.interpreter

import all.model.{
  ZPat,
  Z,
  WildPat,
  Voidd,
  VarPat,
  Var,
  Unitt,
  Type,
  TyVar,
  TrivPat,
  Triv,
  Sum,
  SPat,
  S,
  Rec,
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
import all.model.Unfold
import all.model.Fold
import Substitutor.substT
import all.model.Let
import all.model.All
import all.model.TLam
import all.model.TAp
import all.model.Raise
import all.model.Catch
import all.model.UncaughtException

object Typechecker {

  def typecheck : Expr => Type = typecheckExpr(Map(), Set())

  private def verifyType(delta : Set[String]) : Type => Unit = {
    case Nat => ()
    case Arr(t1, t2) => {
      verifyType(delta)(t1)
      verifyType(delta)(t2)
    }
    case Unitt => ()
    case Prod(t1, t2) => {
      verifyType(delta)(t1)
      verifyType(delta)(t2)
    }
    case Voidd => ()
    case Sum(t1, t2) => {
      verifyType(delta)(t1)
      verifyType(delta)(t2)
    }
    case TyVar(x) =>
      if (delta.contains(x)) ()
      else throw new Exception("type contains unbound tyvar " + x)
    case Rec(x, t) => verifyType(delta + x)(t)
    case All(x, t) => verifyType(delta + x)(t)
  }

  private def typecheckExpr(sigma : Map[String, Type], delta : Set[String]) : Expr => Type = {
    case Var(x) => sigma.getOrElse(x, throw new Exception("unbound variable " + x))
    case Z      => Nat
    case S(e) =>
      if (typecheckExpr(sigma, delta)(e) == Nat) Nat
      else throw new Exception("successor of non-nat " + e)
    case Lam(x, t, e) => {
      verifyType(delta)(t)
      Arr(t, typecheckExpr(sigma + (x -> t), delta)(e))
    }
    case Let(n, d, b) => typecheckExpr(sigma + (n -> typecheckExpr(sigma, delta)(d)), delta)(b)
    case Ap(e1, e2) => typecheckExpr(sigma, delta)(e1) match {
      case Arr(t1, t2) =>
        if (typecheckExpr(sigma, delta)(e2) == t1) t2
        else throw new Exception("application of wrong argument type " + e2)
      case _ => throw new Exception("application of non-function " + e1)
    }
    case Fix(x, t, e) => {
      verifyType(delta)(t)
      if (typecheckExpr(sigma + (x -> t), delta)(e) == t) t
      else throw new Exception("recursive expression does not have declared type " + e)
    }
    case Triv          => Unitt
    case Pairr(e1, e2) => Prod(typecheckExpr(sigma, delta)(e1), typecheckExpr(sigma, delta)(e2))
    case ProjL(e) => typecheckExpr(sigma, delta)(e) match {
      case Prod(t1, t2) => t1
      case _            => throw new Exception("projL of non-product " + e)
    }
    case ProjR(e) => typecheckExpr(sigma, delta)(e) match {
      case Prod(t1, t2) => t2
      case _            => throw new Exception("projR of non-product " + e)
    }
    case Abort(t, e) =>
      if (typecheckExpr(sigma, delta)(e) == Voidd) t
      else throw new Exception("abort of non-void " + e)
    case InL(Sum(t1, t2), e) =>
      if (typecheckExpr(sigma, delta)(e) == t1) Sum(t1, t2)
      else throw new Exception("inL of incompatible left type " + e)
    case InL(t, e) => throw new Exception("inL to non-sum-type " + t)
    case InR(Sum(t1, t2), e) =>
      if (typecheckExpr(sigma, delta)(e) == t2) Sum(t1, t2)
      else throw new Exception("inR of incompatible right type " + e)
    case InR(t, e)    => throw new Exception("inR to non-sum-type " + t)
    case Match(e, rs) => typecheckRules(sigma, delta, rs, typecheckExpr(sigma, delta)(e))
    case Fold(x, t, e) => {
      val t2 = typecheckExpr(sigma, delta)(e)
      if (t2 == substT(x, Rec(x, t))(t)) Rec(x, t)
      else throw new Exception("fold of incorrect recursion type " + e)
    }
    case Unfold(e) => typecheckExpr(sigma, delta)(e) match {
      case Rec(x, t) => substT(x, Rec(x, t))(t)
      case _         => throw new Exception("unfold of non-recursive " + e)
    }
    case TLam(x, e) => All(x, typecheckExpr(sigma, delta + x)(e))
    case TAp(e, t) => typecheckExpr(sigma, delta)(e) match {
      case All(x, t2) => substT(x, t)(t2)
      case _          => throw new Exception("type-application of non-type-function " + e)
    }
    case Raise(t) => {
      verifyType(delta)(t)
      t
    }
    case Catch(e1, e2) => {
      val t = typecheckExpr(sigma, delta)(e1)
      if (typecheckExpr(sigma, delta)(e2) == t) t
      else throw new Exception("try/catch with incompatible types" + e1 + " " + e2)
    }
    case UncaughtException => throw new Exception("typechecking uncaught exception")
  }

  private def typecheckRules(sigma : Map[String, Type], delta : Set[String], rs : List[(Pattern, Expr)], t : Type) : Type = {
    val typ = typecheckRule(sigma, delta, rs.head, t)
    if (rs.forall(r => typecheckRule(sigma, delta, r, t) == typ)) typ
    else throw new Exception("incompatible branches " + rs)
  }

  private def typecheckRule(sigma : Map[String, Type], delta : Set[String], r : (Pattern, Expr), t : Type) : Type = {
    val bind = typecheckPat(r._1, t)
    typecheckExpr(sigma ++ bind, delta)(r._2)
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