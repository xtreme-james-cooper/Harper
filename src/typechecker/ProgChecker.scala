package typechecker

import model.{ TypeDefn, Type, Prog, ExprDefn, Defn }

object ProgChecker extends TypeChecker {

  def typeCheck(p : Prog) : Map[String, Type] = {
    val (finalEnv, finalTyenv) = p.defs.foldLeft(baseEnv)({ case ((env, tyenv), defn) => typeCheck(defn, env, tyenv) })
    finalEnv + ("main" -> CommandChecker.typeCheck(p.e, finalEnv, finalTyenv))
  }

  private def typeCheck(d : Defn, env : Env, tyenv : Env) : (Env, Env) = d match {
    case ExprDefn(n, b, args) => (env + (n -> ExprChecker.typeCheck(b, env ++ args.map({ case (v, t) => (v, t.swap(tyenv)) }), tyenv, Map())), tyenv)
    case TypeDefn(n, t)       => (env, tyenv + (n -> t.swap(tyenv)))
  }

}