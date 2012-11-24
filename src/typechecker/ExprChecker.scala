package typechecker

import model.{ Z, Var, Unknown, UnitTy, Unfold, TypeLam, TypeApp, Type, TryCatch, Triv, ThrowEx, Sum, S, 
  Product, PairEx, Nat, Match, Lam, Inductive, InR, InL, ForAll, Fold, Expr, CommandExp, Arrow, App }

object ExprChecker extends TypeChecker {

  def typeCheck(e : Expr, env : Env, tyenv : Env, as : Env) : Type = {
    val (t, cs) = getType(e, env, tyenv, as)
    verifyConstraints(t, cs)
  }

  def getType(e : Expr, env : Env, tyenv : Env, as : Env) : (Type, List[Constraint]) = e match {
    case Var(x) => (env(x), Nil)
    case Z      => (Nat, Nil)
    case Triv   => (UnitTy, Nil)
    case S(n) => {
      val (t, cs) = getType(n, env, tyenv, as)
      (t, (t, Nat) :: cs)
    }
    case Lam(v, t, e) => {
      val t1 = t.swap(tyenv)
      val (t2, cs) = getType(e, env + (v -> t1), tyenv, as)
      (Arrow(t1, t2), cs)
    }
    case App(e1, e2) => {
      val hole1 = newUnknown
      val hole2 = newUnknown
      val (t1, cs1) = getType(e1, env, tyenv, as)
      val (t2, cs2) = getType(e2, env, tyenv, as)
      (hole2, (t1, Arrow(hole1, hole2)) :: (hole1, t2) :: cs1 ++ cs2)
    }
    case PairEx(e1, e2) => {
      val (t1, cs1) = getType(e1, env, tyenv, as)
      val (t2, cs2) = getType(e2, env, tyenv, as)
      (Product(t1, t2), cs1 ++ cs2)
    }
    case InL(i) => {
      val hole = newUnknown
      val (t3, cs) = getType(i, env, tyenv, as)
      (Sum(t3, hole), cs)
    }
    case InR(i) => {
      val hole = newUnknown
      val (t3, cs) = getType(i, env, tyenv, as)
      (Sum(hole, t3), cs)
    }
    case Match(e, rs) => {
      val (t1, cs1) = getType(e, env, tyenv, as)
      val (t2, cs2) = PatternChecker.getType(rs, t1, env, tyenv, as)
      (t2, cs1 ++ cs2)
    }
    case Fold(mu, t, e) => {
      val t1 = t.swap(tyenv)
      val (t2, cs) = getType(e, env, tyenv, as)
      (Inductive(mu, t1), (t2, t1.swap(mu, Inductive(mu, t1))) :: cs)
    }
    case Unfold(e) => {
      val (t1, cs) = getType(e, env, tyenv, as)
      t1 match {
        case Inductive(mu, t) => (t.swap(mu, Inductive(mu, t)), cs)
        case Unknown(i)       => throw new Exception("unfolding of bad type " + t1) //TODO
        case _                => throw new Exception("unfolding of bad type " + t1)
      }
    }
    case TypeLam(t, e) => {
      val (t1, cs) = getType(e, env, tyenv, as)
      (ForAll(t, t1), cs)
    }
    case TypeApp(e, t) => {
      val (t1, cs) = getType(e, env, tyenv, as)
      t1 match {
        case ForAll(x, t2) => (t2.swap(x, t.swap(tyenv)), cs)
        case Unknown(i)    => throw new Exception("unfolding of bad type " + t1) //TODO
        case _             => throw new Exception("unfolding of bad type " + t1)
      }
    }
    case ThrowEx(s) => (newUnknown, Nil)
    case TryCatch(e1, e2) => {
      val (t1, cs1) = getType(e1, env, tyenv, as)
      val (t2, cs2) = getType(e2, env, tyenv, as)
      (t1, (t1, t2) :: cs1 ++ cs2)
    }
    case CommandExp(m) => CommandChecker.getType(m, env, tyenv, as)
  }

}