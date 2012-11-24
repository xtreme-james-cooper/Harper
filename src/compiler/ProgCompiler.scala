package compiler

import model.{ TypeDefn, Prog, ExprDefn, Defn}

object ProgCompiler {

  def run(p : Prog) : Value = {
    
    //vars to avoid a truely hideous multi-recursive fold
    var code : List[ExprOpcode] = Nil
    var env : Map[String, Value] = Map()
    
    for (ExprDefn(n, b, args) <- p.defs) {
      env = env + (n -> ExprCompiler.run(b, List(env), code))
      code = code ++ ExprCompiler.compileExpr(b)
    }
    
    CommandCompiler.run(p.e, List(env), code)
  }

}