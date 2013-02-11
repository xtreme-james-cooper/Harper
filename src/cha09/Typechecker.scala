package cha09

object Typechecker {

  def typecheck : Expr => Type = typecheckExpr(Map())

  private def typecheckExpr(sigma : Map[String, Type]) : Expr => Type = {
    case Var(x) => sigma.getOrElse(x, throw new Exception("unbound variable " + x))
    case Z => NumTy
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
    case Rec(e0, x, y, e1, e) =>
      if (typecheckExpr(sigma)(e) == NumTy) {
        val t = typecheckExpr(sigma)(e0)
        if (typecheckExpr(sigma + (x -> NumTy) + (y -> t))(e1) == t) t
        else throw new Exception("rec cases do not match " + e0 + " " + e1)
      }
      else throw new Exception("rec of non-num " + e)
  }

}