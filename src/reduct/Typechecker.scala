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

  type Constraint = (Type, Type)

  def assembleConstraints(e : Expr)(env : Env) : (Type, List[Constraint]) = e match {
    case Var(x) => (env(x), Nil)
    case Z      => (Nat, Nil)
    case Triv   => (UnitTy, Nil)
    case S(n) => {
      val (Nat, cs) = assembleConstraints(n)(env)
      (Nat, cs)
    }
    case Lam(v, t, e) => {
      val (t2, cs) = assembleConstraints(e)(env + (v -> t))
      (Arrow(t, t2), cs)
    }
    case App(e1, e2) => {
      val (Arrow(t1, t2), cs1) = assembleConstraints(e1)(env)
      val (t3, cs2) = assembleConstraints(e2)(env)
      (t2, (t1, t3) :: cs1 ++ cs2)
    }
    case Fix(v, t, e) => {
      val (t2, cs) = assembleConstraints(e)(env + (v -> t))
      (t, (t, t2) :: cs)
    }
    case PairEx(e1, e2) => {
      val (t1, cs1) = assembleConstraints(e1)(env)
      val (t2, cs2) = assembleConstraints(e2)(env)
      (Product(t1, t2), cs1 ++ cs2)
    }
    case InL(i, t) => {
      val (t3, cs) = assembleConstraints(i)(env)
      val Sum(t1, t2) = t
      (t, (t3, t1) :: cs)
    }
    case InR(i, t) => {
      val (t3, cs) = assembleConstraints(i)(env)
      val Sum(t1, t2) = t
      (t, (t3, t2) :: cs)
    }
    case Match(e, rs) => {
      val (t1, cs1) = assembleConstraints(e)(env)
      val (t2, cs2) = typeverify(rs)(t1)(env)
      (t2, cs1 ++ cs2)
    }
    case Fold(mu, t, e) => {
      val (t2, cs) = assembleConstraints(e)(env)
      (Inductive(mu, t), (t2, t.swap(mu, Inductive(mu, t))) :: cs)
    }
    case Unfold(e) => {
      val (Inductive(mu, t), cs) = assembleConstraints(e)(env)
      (t.swap(mu, Inductive(mu, t)), cs)
    }
    case TypeLam(t, e) => {
      val (t1, cs) = assembleConstraints(e)(env)
      (ForAll(t, t1), cs)
    }
    case TypeApp(e, t) => {
      val (ForAll(x, t1), cs) = assembleConstraints(e)(env)
      (t1.swap(x, t), cs)
    }
  }

  //t is the type that the pattern is expected to have; under that assumption, it produces some type
  def typeverify(rs : List[Rule])(t : Type)(env : Env) : (Type, List[Constraint]) =
    rs.map(r => typeverify(r)(t)(env)).reduce[(Type, List[Constraint])]({
      case ((t1, cs1), (t2, cs2)) => (t1, (t1, t2) :: cs1 ++ cs2)
    })

  def typeverify(r : Rule)(t : Type)(env : Env) : (Type, List[Constraint]) = assembleConstraints(r.b)(env ++ typeverify(r.p)(t)(env))

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
  
  def typecheck(e : Expr)(env : Env) : Type = {
    val (t, cs) = assembleConstraints(e)(env)
    verifyConstraints(cs)
    t
  }
  
  def verifyConstraints(cs : List[Constraint]) : Unit =
    cs.foreach({ case (t1, t2) => if (! (t1 ~=~ t2)) throw new Exception("Constraint failure: " + t1 + " != " + t2) })

  def typecheck(d : Defn)(env : Env, tyenv : Env) : (Env, Env) = d match {
    case ExprDefn(n, b) => (env + (n -> typecheck(b.typeExpand(tyenv))(env)), tyenv)
    case TypeDefn(n, t) => (env, tyenv + (n -> t.swap(tyenv)))
  }

  type Env = Map[String, Type]

  def baseEnv : (Env, Env) = (Map(), Map())

  def typecheck(p : Prog) : Type = {
    val (finalEnv, finalTyenv) = p.defs.foldLeft(baseEnv)({ case ((env, tyenv), defn) => typecheck(defn)(env, tyenv) })
    typecheck(p.e.typeExpand(finalTyenv))(finalEnv)
  }

}