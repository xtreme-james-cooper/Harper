package interpreter

import model.{ Z, Type, S, Nat, Expr }

object Typechecker {

  def typecheck : Expr => Type = {
    case Z => Nat
    case S(e) =>
      if (typecheck(e) == Nat) Nat
      else throw new Exception("successor of non-nat " + e)
  }

}