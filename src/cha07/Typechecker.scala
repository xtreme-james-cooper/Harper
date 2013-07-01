package cha07

object Typechecker {

  case class UnboundVariable(x : String) extends Exception
  case class TypeMismatch(expected : Type, actual : Type) extends Exception

  def typecheck : Expr => Type = typecheckExpr(Map())

  def typecheckExpr(sigma : Map[String, Type]) : Expr => Type = {
    case Var(x) => sigma.getOrElse(x, throw UnboundVariable(x))
    case Str(s) => StrTy
    case Num(n) => NumTy
    case Plus(e1, e2) =>
      expectType(NumTy, typecheckExpr(sigma)(e1)) {
        expectType(NumTy, typecheckExpr(sigma)(e2)) {
          NumTy
        }
      }
    case Times(e1, e2) =>
      expectType(NumTy, typecheckExpr(sigma)(e1)) {
        expectType(NumTy, typecheckExpr(sigma)(e2)) {
          NumTy
        }
      }
    case Cat(e1, e2) =>
      expectType(StrTy, typecheckExpr(sigma)(e1)) {
        expectType(StrTy, typecheckExpr(sigma)(e2)) {
          StrTy
        }
      }
    case Len(e1) =>
      expectType(StrTy, typecheckExpr(sigma)(e1)) {
        NumTy
      }
    case Let(e1, x, e2) => typecheckExpr(sigma + (x -> typecheckExpr(sigma)(e1)))(e2)
  }

  def expectType[A](expected : Type, actual : Type)(k : => A) : A = if (actual == expected) k else throw TypeMismatch(expected, actual)

}