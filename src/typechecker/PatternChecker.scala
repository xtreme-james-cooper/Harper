package typechecker

import model.{ ZPat, WildPat, VarPat, UnitTy, Type, TrivPat, Sum, SPat, Rule, Product, Pattern, PairPat, Nat, InRPat, InLPat }

object PatternChecker extends TypeChecker {

  //t is the type that the pattern is expected to have; under that assumption, it produces some type for the body
  def getType(rs : List[Rule], t : Type, env : Env, tyenv : Env, as : Env) : (Type, List[Constraint]) =
    rs.map(r => getType(r, t, env, tyenv, as)).reduce[(Type, List[Constraint])]({
      case ((t1, cs1), (t2, cs2)) => (t1, (t1, t2) :: cs1 ++ cs2)
    })

  private def getType(r : Rule, t : Type, env : Env, tyenv : Env, as : Env) : (Type, List[Constraint]) = {
    val (bind, cs1) = typeCheck(r.p, t, env, tyenv);
    val (t0, cs2) = ExprChecker.getType(r.b, env ++ bind, tyenv, as)
    (t0, cs1 ++ cs2)
  }

  //Trying to match against t, it produces a list of variable-type bindings
  private def typeCheck(p : Pattern, t : Type, env : Env, tyenv : Env) : (Map[String, Type], List[Constraint]) = p match {
    case WildPat   => (Map(), Nil)
    case VarPat(x) => (Map(x -> t), Nil)
    case TrivPat   => (Map(), (t, UnitTy) :: Nil)
    case ZPat      => (Map(), (t, Nat) :: Nil)
    case SPat(p) => {
      val (bind, cs) = typeCheck(p, Nat, env, tyenv)
      (bind, (t, Nat) :: cs)
    }
    case PairPat(p1, p2) => {
      val t1 = newUnknown
      val t2 = newUnknown
      val (p1binds, cs1) = typeCheck(p1, t1, env, tyenv)
      val (p2binds, cs2) = typeCheck(p2, t2, env, tyenv)
      if ((p1binds.keySet & p2binds.keySet).isEmpty) (p1binds ++ p2binds, (t, Product(t1, t2)) :: cs1 ++ cs2)
      else throw new Exception("Overlapping pattern variables")
    }
    case InLPat(p) => {
      val t1 = newUnknown
      val t2 = newUnknown
      val (bind, cs) = typeCheck(p, t1, env, tyenv)
      (bind, (t, Sum(t1, t2)) :: cs)
    }
    case InRPat(p) => {
      val t1 = newUnknown
      val t2 = newUnknown
      val (bind, cs) = typeCheck(p, t2, env, tyenv)
      (bind, (t, Sum(t1, t2)) :: cs)
    }
  }

}