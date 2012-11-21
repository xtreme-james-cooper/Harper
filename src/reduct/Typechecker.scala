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
import model.ThrowEx
import model.TryCatch
import model.Command
import model.CommandExp
import model.Ret
import model.Bind
import model.CommandType
import model.Decl
import model.Get
import model.SetCmd

object Typechecker {

  type Constraint = (Type, Type)
  type Env = Map[String, Type]

  def baseEnv : (Env, Env) = (Map(), Map())

  //not semantically a var; done this way to save the effort of piping it around
  var typeVarCounter : Int = 0

  def newUnknown : Type = {
    typeVarCounter = typeVarCounter + 1
    Unknown(typeVarCounter)
  }

  def assembleConstraints(e : Expr, env : Env, tyenv : Env) : (Type, List[Constraint]) = e match {
    case Var(x) => (env(x), Nil)
    case Z      => (Nat, Nil)
    case Triv   => (UnitTy, Nil)
    case S(n) => {
      val (t, cs) = assembleConstraints(n, env, tyenv)
      (t, (t, Nat) :: cs)
    }
    case Lam(v, t, e) => {
      val t1 = t.swap(tyenv)
      val (t2, cs) = assembleConstraints(e, env + (v -> t1), tyenv)
      (Arrow(t1, t2), cs)
    }
    case App(e1, e2) => {
      val hole1 = newUnknown
      val hole2 = newUnknown
      val (t1, cs1) = assembleConstraints(e1, env, tyenv)
      val (t2, cs2) = assembleConstraints(e2, env, tyenv)
      (hole2, (t1, Arrow(hole1, hole2)) :: (hole1, t2) :: cs1 ++ cs2)
    }
    case Fix(v, e) => {
      val t = env(v) //Guarenteed to be there by construction, since Fixes are only built by defs, which enhance the environment 
      val (t2, cs) = assembleConstraints(e, env + (v -> t), tyenv)
      (t, (t, t2) :: cs)
    }
    case PairEx(e1, e2) => {
      val (t1, cs1) = assembleConstraints(e1, env, tyenv)
      val (t2, cs2) = assembleConstraints(e2, env, tyenv)
      (Product(t1, t2), cs1 ++ cs2)
    }
    case InL(i) => {
      val hole = newUnknown
      val (t3, cs) = assembleConstraints(i, env, tyenv)
      (Sum(t3, hole), cs)
    }
    case InR(i) => {
      val hole = newUnknown
      val (t3, cs) = assembleConstraints(i, env, tyenv)
      (Sum(hole, t3), cs)
    }
    case Match(e, rs) => {
      val (t1, cs1) = assembleConstraints(e, env, tyenv)
      val (t2, cs2) = typeverify(rs, t1, env, tyenv)
      (t2, cs1 ++ cs2)
    }
    case Fold(mu, t, e) => {
      val t1 = t.swap(tyenv)
      val (t2, cs) = assembleConstraints(e, env, tyenv)
      (Inductive(mu, t1), (t2, t1.swap(mu, Inductive(mu, t1))) :: cs)
    }
    case Unfold(e) => {
      val (t1, cs) = assembleConstraints(e, env, tyenv)
      t1 match {
        case Inductive(mu, t) => (t.swap(mu, Inductive(mu, t)), cs)
        case Unknown(i)       => throw new Exception("unfolding of bad type " + t1) //TODO
        case _                => throw new Exception("unfolding of bad type " + t1)
      }
    }
    case TypeLam(t, e) => {
      val (t1, cs) = assembleConstraints(e, env, tyenv)
      (ForAll(t, t1), cs)
    }
    case TypeApp(e, t) => {
      val (t1, cs) = assembleConstraints(e, env, tyenv)
      t1 match {
        case ForAll(x, t2) => (t2.swap(x, t.swap(tyenv)), cs)
        case Unknown(i)    => throw new Exception("unfolding of bad type " + t1) //TODO
        case _             => throw new Exception("unfolding of bad type " + t1)
      }
    }
    case ThrowEx(s) => (newUnknown, Nil)
    case TryCatch(e1, e2) => {
      val (t1, cs1) = assembleConstraints(e1, env, tyenv)
      val (t2, cs2) = assembleConstraints(e2, env, tyenv)
      (t1, (t1, t2) :: cs1 ++ cs2)
    }
    case CommandExp(m) => {
      (Nat, checkCommand(m, env, tyenv, Set()))
    }
  }

  //determines if a command has only well-typed expressions in it, and returns any constraints appropriate
  def checkCommand(c : Command, env : Env, tyenv : Env, assignables : Set[String]) : List[Constraint] = c match {
    case Ret(e) => {
      val (t, cs) = assembleConstraints(e, env, tyenv)
      (t, Nat) :: cs
    }
    case Bind(x, e, m) => {
      val (t, cs1) = assembleConstraints(e, env, tyenv)
      val cs2 = checkCommand(m, env + (x -> Nat), tyenv, assignables)
      (t, CommandType) :: cs1 ++ cs2
    }
    case Decl(x, e, m) => {
      val (t, cs1) = assembleConstraints(e, env, tyenv)
      val cs2 = checkCommand(m, env, tyenv, assignables + x)
      (t, Nat) :: cs1 ++ cs2
    }
    case Get(x) if assignables.contains(x) => Nil
    case Get(x)                            => throw new Exception("Undeclared assignable " + x)
    case SetCmd(x, e, m) if assignables.contains(x) => {
      val (t, cs1) = assembleConstraints(e, env, tyenv)
      val cs2 = checkCommand(m, env, tyenv, assignables)
      (t, Nat) :: cs1 ++ cs2
    }
    case SetCmd(x, e, m) => throw new Exception("Undeclared assignable " + x)
  }

  //t is the type that the pattern is expected to have; under that assumption, it produces some type
  def typeverify(rs : List[Rule], t : Type, env : Env, tyenv : Env) : (Type, List[Constraint]) =
    rs.map(r => typeverify(r, t, env, tyenv)).reduce[(Type, List[Constraint])]({
      case ((t1, cs1), (t2, cs2)) => (t1, (t1, t2) :: cs1 ++ cs2)
    })

  def typeverify(r : Rule, t : Type, env : Env, tyenv : Env) : (Type, List[Constraint]) = {
    val (bind, cs1) = typeverify(r.p, t, env, tyenv);
    val (t0, cs2) = assembleConstraints(r.b, env ++ bind, tyenv)
    (t0, cs1 ++ cs2)
  }

  //Trying to match against t, it produces a list of variable-type bindings
  def typeverify(p : Pattern, t : Type, env : Env, tyenv : Env) : (Map[String, Type], List[Constraint]) = p match {
    case WildPat   => (Map(), Nil)
    case VarPat(x) => (Map(x -> t), Nil)
    case TrivPat   => (Map(), (t, UnitTy) :: Nil)
    case ZPat      => (Map(), (t, Nat) :: Nil)
    case SPat(p) => {
      val (bind, cs) = typeverify(p, Nat, env, tyenv)
      (bind, (t, Nat) :: cs)
    }
    case PairPat(p1, p2) => {
      val t1 = newUnknown
      val t2 = newUnknown
      val (p1binds, cs1) = typeverify(p1, t1, env, tyenv)
      val (p2binds, cs2) = typeverify(p2, t2, env, tyenv)
      if ((p1binds.keySet & p2binds.keySet).isEmpty) (p1binds ++ p2binds, (t, Product(t1, t2)) :: cs1 ++ cs2)
      else throw new Exception("Overlapping pattern variables")
    }
    case InLPat(p) => {
      val t1 = newUnknown
      val t2 = newUnknown
      val (bind, cs) = typeverify(p, t1, env, tyenv)
      (bind, (t, Sum(t1, t2)) :: cs)
    }
    case InRPat(p) => {
      val t1 = newUnknown
      val t2 = newUnknown
      val (bind, cs) = typeverify(p, t2, env, tyenv)
      (bind, (t, Sum(t1, t2)) :: cs)
    }
  }

  def typecheck(e : Expr, env : Env, tyenv : Env) : Type = {
    val (t, cs) = assembleConstraints(e, env, tyenv)
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

  def typecheck(d : Defn, env : Env, tyenv : Env) : (Env, Env) = d match {
    case ExprDefn(n, b, args) => (env + (n -> typecheck(b, env ++ args.map({ case (v, t) => (v, t.swap(tyenv)) }), tyenv)), tyenv)
    case TypeDefn(n, t)       => (env, tyenv + (n -> t.swap(tyenv)))
  }

  def typecheck(p : Prog) : Map[String, Type] = {
    val (finalEnv, finalTyenv) = p.defs.foldLeft(baseEnv)({ case ((env, tyenv), defn) => typecheck(defn, env, tyenv) })
    finalEnv + ("main" -> typecheck(p.e, finalEnv, finalTyenv))
  }

}