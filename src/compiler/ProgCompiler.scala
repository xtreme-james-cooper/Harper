package compiler

import model.{ TypeDefn, Prog, Lam, ExprDefn, Defn, Command }

object ProgCompiler {

  def run(p : Prog) : Value = innerRun(p.e, p.defs, Map(), Nil)

  def innerRun(e : Command, defs : List[Defn], env : Map[String, Value], code : List[ExprOpcode]) : Value = defs match {
    case Nil                                   => CommandCompiler.run(e, List(env), code)
    case TypeDefn(_, _) :: ds                  => innerRun(e, ds, env, code)
    case ExprDefn(n, b, args) :: ds            => {
      val newcode = ExprCompiler.compileExpr(b)
      innerRun(e, ds, env + (n -> ExprCPU.run(newcode ++ List(ExprExit) ++ code, List(env))), code ++ newcode)
    }
  }

}