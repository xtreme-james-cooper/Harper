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
import model.Unknown

object Typechecker {

  type Constraint = (Type, Type)

  //not semantically a var; done this way to save the effort of piping it around
  var typeVarCounter : Int = 0

  def newUnknown : Type = {
    typeVarCounter = typeVarCounter + 1
    Unknown(typeVarCounter)
  }
  
  def newBindingName : String = {
    typeVarCounter = typeVarCounter + 1
    "#" + typeVarCounter //safe because #2 is unparseable as a var
  }
  
  def assembleConstraints(e : Expr)(env : Env) : (Type, List[Constraint]) = {
//    println(e + " in " + env)
    val (t, cs) = assembleConstraints_(e)(env)
//    println(t + " and " + cs)
    (t, cs)
  }

  def assembleConstraints_(e : Expr)(env : Env) : (Type, List[Constraint]) = e match {
    case Var(x) => (env(x), Nil)
    case Z      => (Nat, Nil)
    case Triv   => (UnitTy, Nil)
    case S(n) => {
      val (t, cs) = assembleConstraints(n)(env)
      (t, (t, Nat) :: cs)
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
    case InL(i) => {
      val hole = newUnknown
      val (t3, cs) = assembleConstraints(i)(env)
      (Sum(t3, hole), cs)
    }
    case InR(i) => {
      val hole = newUnknown
      val (t3, cs) = assembleConstraints(i)(env)
      (Sum(hole, t3), cs)
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
      val hole = newUnknown
      val bind = newBindingName
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
    rs.map(r => typeverify(r, t, env)).reduce[(Type, List[Constraint])]({
      case ((t1, cs1), (t2, cs2)) => (t1, (t1, t2) :: cs1 ++ cs2)
    })

  def typeverify(r : Rule, t : Type, env : Env) : (Type, List[Constraint]) = {
    val (bind, cs1) = typeverify(r.p, t, env);
    val (t0, cs2) = assembleConstraints(r.b)(env ++ bind)
    (t0, cs1 ++ cs2)
  }

  //Trying to match against t, it produces a list of variable-type bindings
  def typeverify(p : Pattern, t : Type, env : Env) : (Map[String, Type], List[Constraint]) = p match {
    case WildPat   => (Map(), Nil)
    case VarPat(x) => (Map(x -> t), Nil)
    case TrivPat   => (Map(), (t, UnitTy) :: Nil)
    case ZPat      => (Map(), (t, Nat) :: Nil)
    case SPat(p) => {
      val (bind, cs) = typeverify(p, Nat, env)
      (bind, (t, Nat) :: cs)
    }
    case PairPat(p1, p2) => {
      val t1 = newUnknown
      val t2 = newUnknown
      val (p1binds, cs1) = typeverify(p1, t1, env)
      val (p2binds, cs2) = typeverify(p2, t2, env)
      if ((p1binds.keySet & p2binds.keySet).isEmpty) (p1binds ++ p2binds, (t, Product(t1, t2)) :: cs1 ++ cs2)
      else throw new Exception("Overlapping pattern variables")
    }
    case InLPat(p) => {
      val t1 = newUnknown
      val t2 = newUnknown
      val (bind, cs) = typeverify(p, t1, env)
      (bind, (t, Sum(t1, t2)) :: cs)
    }
    case InRPat(p) => {
      val t1 = newUnknown
      val t2 = newUnknown
      val (bind, cs) = typeverify(p, t2, env)
      (bind, (t, Sum(t1, t2)) :: cs)
    }
  }

  def typecheck(e : Expr)(env : Env) : Type = {
    val (t, cs) = assembleConstraints(e)(env)
    verifyConstraints(t, cs)
  }

  def verifyConstraints(t : Type, cs : List[Constraint]) : Type = cs.flatMap({ case (t1, t2) => t1 ~=~ t2 }) match {
    case Nil                           => t
    case (Unknown(i), b) :: cs         => verifyConstraints(t.swap(i, b), cs.map({ case (x, y) => (x.swap(i, b), y.swap(i, b)) }))
    case (a, Unknown(i)) :: cs         => verifyConstraints(t.swap(i, a), cs.map({ case (x, y) => (x.swap(i, a), y.swap(i, a)) }))
    case (t1, t2) :: cs if !(t1 == t2) => throw new Exception("Constraint failure: " + t1 + " != " + t2)
    case (t1, t2) :: cs                => verifyConstraints(t, cs)
  }

  //Replace unknowns that we have information about
  def updateConstraint(unkId : Int, t2 : Type)(cs : List[Constraint]) : List[Constraint] =
    cs.map({ case (a, b) => (a.swap(unkId, t2), b.swap(unkId, t2)) })

  def typecheck(d : Defn)(env : Env, tyenv : Env) : (Env, Env) = d match {
    case ExprDefn(n, b) => (env + (n -> typecheck(b.typeExpand(tyenv))(env)), tyenv)
    case TypeDefn(n, t) => (env, tyenv + (n -> t.swap(tyenv)))
  }

  type Env = Map[String, Type]

  def baseEnv : (Env, Env) = (Map(), Map())

  def typecheck(p : Prog) : Map[String, Type] = {
    val (finalEnv, finalTyenv) = p.defs.foldLeft(baseEnv)({ case ((env, tyenv), defn) => typecheck(defn)(env, tyenv) })
    finalEnv + ("main" -> typecheck(p.e.typeExpand(finalTyenv))(finalEnv))
  }

}