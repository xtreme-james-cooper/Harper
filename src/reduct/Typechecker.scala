package reduct

import model.Type
import model.Var
import model.Expr
import model.S
import model.Z
import model.Nat
import model.App
import model.Lam
import model.Prog
import model.Defn
import model.ExprDefn
import model.Fix
import model.Arrow
import model.Triv
import model.UnitTy
import model.PairEx
import model.Product
import model.InL
import model.InR
import model.Sum
import model.Match
import model.Rule
import model.Pattern
import model.WildPat
import model.VarPat
import model.TrivPat
import model.SPat
import model.PairPat
import model.ZPat
import model.InLPat
import model.InRPat
import model.TyVar
import model.Fold
import model.Inductive
import model.Unfold
import model.TypeLam
import model.ForAll
import model.TypeApp
import model.TypeDefn

object Typechecker {

  def typecheck(e : Expr)(env : Env) : Option[Type] = e match {
    case Var(x) => env.get(x)
    case Z      => Some(Nat)
    case Triv   => Some(UnitTy)
    case S(n) =>
      for {
        Nat <- typecheck(n)(env)
      } yield Nat
    case Lam(v, t, e) =>
      for {
        t2 <- typecheck(e)(env + (v -> t))
      } yield Arrow(t, t2)
    case App(e1, e2) =>
      for {
        Arrow(t1, t2) <- typecheck(e1)(env)
        t3 <- typecheck(e2)(env)
        if typeEq(t1, t3)
      } yield t2
    case Fix(v, t, e) =>
      for {
        t2 <- typecheck(e)(env + (v -> t))
        if typeEq(t, t2)
      } yield t
    case PairEx(e1, e2) =>
      for {
        t1 <- typecheck(e1)(env)
        t2 <- typecheck(e2)(env)
      } yield Product(t1, t2)
    case InL(i, t) =>
      for {
        t3 <- typecheck(i)(env)
        Sum(t1, t2) = t
        if typeEq(t3, t1)
      } yield t
    case InR(i, t) =>
      for {
        t3 <- typecheck(i)(env)
        Sum(t1, t2) = t
        if typeEq(t3, t2)
      } yield t
    case Match(e, rs) =>
      for {
        t1 <- typecheck(e)(env)
        t2 <- typeverify(rs)(t1)(env)
      } yield t2
    case Fold(mu, t, e) =>
      for {
        t2 <- typecheck(e)(env)
        if typeEq(t2, typeSwap(mu, Inductive(mu, t))(t))
      } yield Inductive(mu, t)
    case Unfold(e) =>
      for {
        Inductive(mu, t) <- typecheck(e)(env)
      } yield typeSwap(mu, Inductive(mu, t))(t)
    case TypeLam(t, e) => {
      for {
        t1 <- typecheck(e)(env)
      } yield ForAll(t, t1)
    }
    case TypeApp(e, t) => {
      for {
        ForAll(x, t1) <- typecheck(e)(env)
      } yield typeSwap(x, t)(t1)
    }
  }

  //t is the type that the pattern is expected to have; under that assumption, it produces some type
  def typeverify(rs : List[Rule])(t : Type)(env : Env) : Option[Type] =
    rs.map(r => typeverify(r)(t)(env)).reduce[Option[Type]]({
      case (Some(t1), Some(t2)) if typeEq(t1, t2) => Some(t1)
      case (t1, t2)             => throw new Exception("Noncompatible types " + t1 + " and " + t2)
    })

  def typeverify(r : Rule)(t : Type)(env : Env) : Option[Type] = typecheck(r.b)(env ++ typeverify(r.p)(t)(env))

  //Trying to match against t, it produces a list of variable-type bindings
  def typeverify(p : Pattern)(t : Type)(env : Env) : Map[String, Type] = (p, t) match {
    case (WildPat, t)      => Map()
    case (VarPat(x), t)    => Map(x -> t)
    case (TrivPat, UnitTy) => Map()
    case (ZPat, Nat)       => Map()
    case (SPat(p), Nat)    => typeverify(p)(Nat)(env)
    case (PairPat(p1, p2), Product(t1, t2)) => {
      val p1binds = typeverify(p1)(t1)(env)
      val p2binds = typeverify(p2)(t2)(env)
      if ((p1binds.keySet & p2binds.keySet).isEmpty) p1binds ++ p2binds
      else throw new Exception("Overlapping pattern variables")
    }
    case (InLPat(p), Sum(t1, t2)) => typeverify(p)(t1)(env)
    case (InRPat(p), Sum(t1, t2)) => typeverify(p)(t2)(env)
    case (p, t)                   => throw new Exception("Pattern " + p + " cannot match type " + t)
  }

  def typecheck(d : Defn)(env : Env, tyenv : Env) : (Env, Env) = d match {
    case ExprDefn(n, b) => (env + (n -> typecheck(typeExpand(tyenv)(b))(env).get), tyenv)
    case TypeDefn(n, t) => (env, tyenv + (n -> typeSwap(tyenv)(t)))
  }

  type Env = Map[String, Type]

  def baseEnv : (Env, Env) = (Map(), Map())

  def typecheck(p : Prog) : Option[Type] = {
    val (finalEnv, finalTyenv) = p.defs.foldLeft(baseEnv)({ case ((env, tyenv), defn) => typecheck(defn)(env, tyenv) })
    typecheck(typeExpand(finalTyenv)(p.e))(finalEnv)
  }
  
  
  //Utilities
  
  //replace all type variables mu with x
  def typeSwap(mu : String, x : Type) : Type => Type = {
    case Nat                         => Nat
    case Arrow(t1, t2)               => Arrow(typeSwap(mu, x)(t1), typeSwap(mu, x)(t2))
    case UnitTy                      => UnitTy
    case Product(t1, t2)             => Product(typeSwap(mu, x)(t1), typeSwap(mu, x)(t2))
    case Sum(t1, t2)                 => Sum(typeSwap(mu, x)(t1), typeSwap(mu, x)(t2))
    case TyVar(y) if y == mu         => x
    case TyVar(y)                    => TyVar(y)
    case Inductive(y, t1) if y == mu => Inductive(y, t1)
    case Inductive(y, t1)            => Inductive(y, typeSwap(mu, x)(t1))
    case ForAll(y, t1) if y == mu    => ForAll(y, t1)
    case ForAll(y, t1)               => ForAll(y, typeSwap(mu, x)(t1))
  }
  
  def typeSwap(tyenv : Env)(t : Type) : Type = tyenv.foldLeft(t)({ case (t, (syn, x)) => typeSwap(syn, x)(t) })

  //expand type synonyms syn with x
  def typeExpand(syn : String, x : Type) : Expr => Expr = {
    //Safe to ignore bindings in Fold and TyLam because TySyns must be uppercase strings and TyVars must be lowercase
    case Var(x)         => Var(x)
    case Z              => Z
    case S(n)           => S(typeExpand(syn, x)(n))
    case Lam(v, t, e)   => Lam(v, typeSwap(syn, x)(t), typeExpand(syn, x)(e))
    case App(e1, e2)    => App(typeExpand(syn, x)(e1), typeExpand(syn, x)(e2))
    case Fix(v, t, e)   => Fix(v, typeSwap(syn, x)(t), typeExpand(syn, x)(e))
    case Triv           => Triv
    case PairEx(e1, e2) => PairEx(typeExpand(syn, x)(e1), typeExpand(syn, x)(e2))
    case InL(e, t)      => InL(typeExpand(syn, x)(e), typeSwap(syn, x)(t))
    case InR(e, t)      => InR(typeExpand(syn, x)(e), typeSwap(syn, x)(t))
    case Match(e, rs)   => Match(typeExpand(syn, x)(e), rs.map({ case Rule(p, b) => Rule(p, typeExpand(syn, x)(b)) }))
    case Fold(mu, t, e) => Fold(mu, typeSwap(syn, x)(t), typeExpand(syn, x)(e))
    case Unfold(e)      => Unfold(typeExpand(syn, x)(e))
    case TypeLam(t, e)  => TypeLam(t, typeExpand(syn, x)(e))
    case TypeApp(e, t)  => TypeApp(typeExpand(syn, x)(e), typeSwap(syn, x)(t))
  }

  def typeExpand(tyenv : Env)(e : Expr) : Expr = tyenv.foldLeft(e)({ case (e, (syn, x)) => typeExpand(syn, x)(e) })

  //More precise version of == that allows for alpha-renaming
  def typeEq(t1 : Type, t2 : Type) : Boolean = (t1, t2) match {
    case (Inductive(x, st1), Inductive(y, st2)) => typeEq(st1, typeSwap(y, TyVar(x))(st2))
    case (ForAll(x, st1), ForAll(y, st2))       => typeEq(st1, typeSwap(y, TyVar(x))(st2))
    case (Nat, Nat)                             => true
    case (Arrow(t1, t2), Arrow(t3, t4))         => typeEq(t1, t3) && typeEq(t2, t4)
    case (UnitTy, UnitTy)                       => true
    case (Product(t1, t2), Product(t3, t4))     => typeEq(t1, t3) && typeEq(t2, t4)
    case (Sum(t1, t2), Sum(t3, t4))             => typeEq(t1, t3) && typeEq(t2, t4)
    case (TyVar(x), TyVar(y))                   => x == y
    case (_, _)                                 => false
  }


}