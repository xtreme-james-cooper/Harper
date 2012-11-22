package compiler

import model.{Value, TypeDefn, Prog, ExprDefn, Defn}

object ProgCompiler {

  private def evalDefn(m : Map[String, Value], d : Defn) : Map[String, Value] = d match {
    case ExprDefn(n, b, args) => m + (n -> ExprCompiler.run(b, List(m)))
    case TypeDefn(n, t)       => m
  }

  def run(p : Prog) : Value = CommandCompiler.run(p.e, List(p.defs.foldLeft(Map[String, Value]())(evalDefn)))

}