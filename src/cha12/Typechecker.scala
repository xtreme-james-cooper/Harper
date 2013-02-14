package cha12

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
    case IfZ(e, e0, x, e1) =>
      if (typecheckExpr(sigma)(e) == NumTy) {
        val t = typecheckExpr(sigma)(e0)
        if (typecheckExpr(sigma + (x -> NumTy))(e1) == t) t
        else throw new Exception("ifz cases do not match " + e0 + " " + e1)
      } else throw new Exception("ifz of non-num " + e)
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
    case Case(e, x, e0, y, e1) =>  typecheckExpr(sigma)(e) match {
      case SumTy(t1, t2) => {
        val t = typecheckExpr(sigma + (x -> t1))(e0)
        if (typecheckExpr(sigma + (y -> t2))(e1) == t) t
        else throw new Exception("case arms do not match " + e0 + " " + e1)
      }
      case _ => throw new Exception("case of non-sum " + e)
    }
  }

}