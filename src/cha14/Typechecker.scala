package cha14

object Typechecker {

  def typecheck : Expr => Type = typecheckExpr(Map())

  private def typecheckExpr(sigma : Map[String, Type]) : Expr => Type = {
    case Var(x) => sigma.getOrElse(x, throw new Exception("unbound variable " + x))
    case Z      => NumTy
    case S(e) =>
      if (typecheckExpr(sigma)(e) == NumTy) NumTy
      else throw new Exception("succ of non-num " + e)
    case Let(e1, x, e2) => typecheckExpr(sigma + (x -> typecheckExpr(sigma)(e1)))(e2)
    case Lam(t, x, e)   => ArrTy(t, typecheckExpr(sigma + (x -> t))(e))
    case Ap(e1, e2) => typecheckExpr(sigma)(e1) match {
      case ArrTy(t1, t2) =>
        if (typecheckExpr(sigma)(e2) == t1) t2
        else throw new Exception("appl of incompatible " + e1 + " " + e2)
      case _ => throw new Exception("appl of non-fun " + e1)
    }
    case Fix(t, x, e) =>
      if (typecheckExpr(sigma + (x -> t))(e) == t) t
      else throw new Exception("rec does not match declared type " + t + " " + e)
    case Pair(e1, e2) => ProdTy(typecheckExpr(sigma)(e1), typecheckExpr(sigma)(e2))
    case PrR(e) => typecheckExpr(sigma)(e) match {
      case ProdTy(t1, t2) => t2
      case _              => throw new Exception("projr of non-pair " + e)
    }
    case PrL(e) => typecheckExpr(sigma)(e) match {
      case ProdTy(t1, t2) => t1
      case _              => throw new Exception("projl of non-pair " + e)
    }
    case Triv => UnitTy
    case Abort(t, e) => typecheckExpr(sigma)(e) match {
      case VoidTy => t
      case _      => throw new Exception("abort of non-void " + e)
    }
    case InL(t, e) => t match {
      case SumTy(t1, t2) =>
        if (typecheckExpr(sigma)(e) == t1) t
        else throw new Exception("inl does not match declared type " + t + " " + e)
      case _ => throw new Exception("inl declared type a non-sum " + t)
    }
    case InR(t, e) => t match {
      case SumTy(t1, t2) =>
        if (typecheckExpr(sigma)(e) == t2) t
        else throw new Exception("inr does not match declared type " + t + " " + e)
      case _ => throw new Exception("inr declared type a non-sum " + t)
    }
    case Match(e, rs) => typecheckRules(sigma, rs, typecheckExpr(sigma)(e))
    case Generic(tx, t, x, xt, e0, e) =>
      if (typeExists(tx)(t)) {
        val e0type = typecheckExpr(sigma + (x -> xt))(e0)
        val etype = subst(tx, xt)(t)
        if (typecheckExpr(sigma)(e) == etype) {
          subst(tx, e0type)(t)
        } else throw new Exception(e + " has wrong type")
      } else throw new Exception("type " + t + " contains invalid type var")
  }

  private def typecheckRules(sigma : Map[String, Type], rs : List[(Pattern, Expr)], t : Type) : Type = {
    val typ = typecheckRule(sigma, rs.head, t)
    if (rs.forall(r => typecheckRule(sigma, r, t) == typ)) typ
    else throw new Exception("incompatible branches " + rs)
  }

  private def typecheckRule(sigma : Map[String, Type], r : (Pattern, Expr), t : Type) : Type = {
    val bind = typecheckPat(r._1, t)
    typecheckExpr(sigma ++ bind)(r._2)
  }

  private def typecheckPat : (Pattern, Type) => Map[String, Type] = {
    case (WildPat, _)      => Map()
    case (VarPat(x), t)    => Map(x -> t)
    case (TrivPat, UnitTy) => Map()
    case (TrivPat, t)      => throw new Exception("got unit for type " + t)
    case (PairPat(p1, p2), ProdTy(t1, t2)) => {
      val m1 = typecheckPat(p1, t1)
      val m2 = typecheckPat(p2, t2)
      if (m1.keySet & m2.keySet isEmpty) m1 ++ m2
      else throw new Exception("overlapping variables " + (m1.keySet & m2.keySet))
    }
    case (PairPat(p1, p2), t)       => throw new Exception("got product for type " + t)
    case (InLPat(p), SumTy(t1, t2)) => typecheckPat(p, t1)
    case (InLPat(p), t)             => throw new Exception("got sum for type " + t)
    case (InRPat(p), SumTy(t1, t2)) => typecheckPat(p, t2)
    case (InRPat(p), t)             => throw new Exception("got sum for type " + t)
    case (ZPat, NumTy)              => Map()
    case (ZPat, t)                  => throw new Exception("got nat for type " + t)
    case (SPat(p), NumTy)           => typecheckPat(p, NumTy)
    case (SPat(p), t)               => throw new Exception("got nat for type " + t)
  }

  private def typeExists(t : String) : Type => Boolean = {
    case VarTy(x)       => t == x
    case NumTy          => true
    case ArrTy(t1, t2)  => typeExists(t)(t1) && typeExists(t)(t2)
    case ProdTy(t1, t2) => typeExists(t)(t1) && typeExists(t)(t2)
    case UnitTy         => true
    case VoidTy         => true
    case SumTy(t1, t2)  => typeExists(t)(t1) && typeExists(t)(t2)
  }

  private def subst(x : String, t : Type) : Type => Type = {
    case VarTy(y)       => if (y == x) t else VarTy(y)
    case NumTy          => NumTy
    case ArrTy(t1, t2)  => ArrTy(subst(x, t)(t1), subst(x, t)(t2))
    case ProdTy(t1, t2) => ProdTy(subst(x, t)(t1), subst(x, t)(t2))
    case UnitTy         => UnitTy
    case VoidTy         => VoidTy
    case SumTy(t1, t2)  => SumTy(subst(x, t)(t1), subst(x, t)(t2))
  }

}