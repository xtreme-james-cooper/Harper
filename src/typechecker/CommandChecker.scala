package typechecker

import model.{ Type, SetCmd, Ret, Get, Decl, CommandTy, Command, Bind }

object CommandChecker extends TypeChecker {

  def typeCheck(c : Command, env : Env, tyenv : Env) : Type = {
    val (t, cs) = getType(c, env, tyenv, Map())
    verifyConstraints(t, cs)
  }

  def getType(c : Command, env : Env, tyenv : Env, assignables : Env) : (Type, List[Constraint]) = c match {
    case Ret(e) => {
      val (t, cs) = ExprChecker.getType(e, env, tyenv, assignables)
      (CommandTy(t), cs)
    }
    case Bind(x, e, m) => {
      val hole = newUnknown
      val (t, cs1) = ExprChecker.getType(e, env, tyenv, assignables)
      val (t2, cs2) = getType(m, env + (x -> hole), tyenv, assignables)
      (t2, (t, CommandTy(hole)) :: cs1 ++ cs2)
    }
    case Decl(x, e, m) => {
      val (t, cs1) = ExprChecker.getType(e, env, tyenv, assignables)
      val (t2, cs2) = getType(m, env, tyenv, assignables + (x -> t))
      (t2, cs1 ++ cs2)
    }
    case Get(x) if assignables.contains(x) => (CommandTy(assignables(x)), Nil)
    case Get(x)                            => throw new Exception("Undeclared assignable " + x + " " + assignables)
    case SetCmd(x, e, m) if assignables.contains(x) => {
      val (t, cs1) = ExprChecker.getType(e, env, tyenv, assignables)
      val (t2, cs2) = getType(m, env, tyenv, assignables)
      (t2, cs1 ++ cs2)
    }
    case SetCmd(x, e, m) => throw new Exception("Undeclared assignable " + x + " " + assignables)
  }

}