package cha07

object Typechecker {

  def typecheck : Expr => Type = typecheckExpr(Map())

  private def typecheckExpr(sigma : Map[String, Type]) : Expr => Type = {
    case Var(x) => sigma.getOrElse(x, throw new Exception("unbound variable " + x))
    case Str(s) => StrTy
    case Num(n) => NumTy
    case Plus(e1, e2) =>
      if (typecheckExpr(sigma)(e1) == NumTy && typecheckExpr(sigma)(e2) == NumTy) NumTy
      else throw new Exception("plus of non-nums " + e1 + " " + e2)
    case Times(e1, e2) =>
      if (typecheckExpr(sigma)(e1) == NumTy && typecheckExpr(sigma)(e2) == NumTy) NumTy
      else throw new Exception("times of non-nums " + e1 + " " + e2)
    case Cat(e1, e2) =>
      if (typecheckExpr(sigma)(e1) == StrTy && typecheckExpr(sigma)(e2) == StrTy) StrTy
      else throw new Exception("cat of non-strs " + e1 + " " + e2)
    case Len(e1) =>
      if (typecheckExpr(sigma)(e1) == StrTy) NumTy
      else throw new Exception("len of non-str " + e1)
    case Let(e1, x, e2) => typecheckExpr(sigma + (x -> typecheckExpr(sigma)(e1)))(e2)
  }

}