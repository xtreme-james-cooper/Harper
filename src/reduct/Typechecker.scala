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

object Typechecker {

  def typecheck(e : Expr)(env : Env) : Option[Type] = e match {
    case Var(x) => env.bindings.get(x)
    case Z      => Some(Nat)
    case Triv   => Some(UnitTy)
    case S(n) =>
      for {
        Nat <- typecheck(n)(env)
      } yield Nat
    case Lam(v, t, e) =>
      for {
        t2 <- typecheck(e)(env.addBind(v -> t.replace(env.typeSyns)))
      } yield Arrow(t.replace(env.typeSyns), t2)
    case App(e1, e2) =>
      for {
        Arrow(t1, t2) <- typecheck(e1)(env)
        t3 <- typecheck(e2)(env)
        if t1 == t3
      } yield t2
    case Fix(v, t, e) =>
      for {
        t2 <- typecheck(e)(env.addBind(v -> t.replace(env.typeSyns)))
        tnorm = t.replace(env.typeSyns)
        if tnorm == t2
      } yield tnorm
    case PairEx(e1, e2) =>
      for {
        t1 <- typecheck(e1)(env)
        t2 <- typecheck(e2)(env)
      } yield Product(t1, t2)
    case InL(i, t) =>
      for {
        t3 <- typecheck(i)(env)
        Sum(t1, t2) = t.replace(env.typeSyns)
        if t3 == t1
      } yield t.replace(env.typeSyns)
    case InR(i, t) =>
      for {
        t3 <- typecheck(i)(env)
        Sum(t1, t2) = t.replace(env.typeSyns)
        if t3 == t2
      } yield t.replace(env.typeSyns)
    case Match(e, rs) =>
      for {
        t1 <- typecheck(e)(env)
        t2 <- typeverify(rs)(t1)(env)
      } yield t2
  }

  //t is the type that the pattern is expected to have; under that assumption, it produces some type
  def typeverify(rs : List[Rule])(t : Type)(env : Env) : Option[Type] = 
    rs.map(r => typeverify(r)(t)(env)).reduce[Option[Type]]({case (t1, t2) if t1 == t2 => t1})
  
  def typeverify(r : Rule)(t : Type)(env : Env) : Option[Type] = typecheck(r.b)(env.addBinds(typeverify(r.p)(t)(env)))
  
  //Trying to match against t, it produces a list of variable-type bindings
  def typeverify(p : Pattern)(t : Type)(env : Env) : Map[String, Type] = (p, t) match {
    case (WildPat, t) => Map()
    case (VarPat(x), t) => Map(x -> t)
    case (TrivPat, UnitTy) => Map()
    case (ZPat, Nat) => Map()
    case (SPat(p), Nat) => typeverify(p)(Nat)(env)
    case (PairPat(p1, p2), Product(t1, t2)) => {
      val p1binds = typeverify(p1)(t1)(env) 
      val p2binds = typeverify(p2)(t2)(env)
      if ((p1binds.keySet & p2binds.keySet).isEmpty) p1binds ++ p2binds
      else throw new Exception("Overlapping pattern variables")
    }
    case (InLPat(p), Sum(t1, t2)) => typeverify(p)(t1)(env)
    case (InRPat(p), Sum(t1, t2)) => typeverify(p)(t2)(env)
  }
    
  def typecheck(d : Defn)(env : Env) : Env = d match {case Defn(n, b) => env.addBind(n -> typecheck(b)(env).get)}

  class Env(val typeSyns : Map[String, Type], val bindings : Map[String, Type]) {
    def addSyn(syn : (String, Type)) : Env = new Env(typeSyns + syn, bindings)
    def addBind(bind : (String, Type)) : Env = new Env(typeSyns, bindings + bind)
    def addBinds(binds : Map[String, Type]) : Env = new Env(typeSyns, bindings ++ binds)
  }

  def baseEnv : Env = new Env(Map("Nat" -> Nat, "Unit" -> UnitTy), Map())

  def typecheck(p : Prog) : Option[Type] =
    typecheck(p.e)(p.defs.foldLeft(baseEnv)({ case (env, defn) => typecheck(defn)(env) }))

}