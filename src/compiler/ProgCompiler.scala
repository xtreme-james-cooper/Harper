package compiler

import model.{ TypeDefn, Prog, Lam, ExprDefn, Defn, Command }

object ProgCompiler {

  def run(p : Prog) : Value = innerRun(p.e, p.defs, Map(), Nil)

  def innerRun(e : Command, defs : List[Defn], env : Map[String, Value], code : List[ExprOpcode]) : Value = defs match {
    case Nil                                   => CommandCompiler.run(e, List(env), code)
    case TypeDefn(_, _) :: ds                  => innerRun(e, ds, env, code)
    case ExprDefn(n, Lam(x, t, b), args) :: ds => innerRun(e, ds, env + (n -> RecursiveLamVal(n, x, env)), code ++ ExprCompiler.compileSubroutine(n, b))
    case ExprDefn(n, b, args) :: ds            => innerRun(e, ds, env + (n -> ExprCompiler.run(b, List(env), code)), code ++ ExprCompiler.compileExpr(b))
  }

}