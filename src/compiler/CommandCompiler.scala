package compiler

import model.{ Value, SetCmd, Ret, Get, Decl, Command, Bind, Action }

object CommandCompiler {

  sealed abstract class CmdStack(name : String) {
    override def toString : String = name
  }

  def getBinding(e : List[Map[String, Value]], x : String) : Value = e match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m(x)
    case m :: e                  => getBinding(e, x)
  }

  //Update the outermost stack-bound x
  private def updateMemory(x : String, v : Value, mem : List[Map[String, Value]]) : List[Map[String, Value]] = innerUpdateMemory(x, v, mem)
  private def innerUpdateMemory(x : String, v : Value, m : List[Map[String, Value]]) : List[Map[String, Value]] = m match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m + (x -> v) :: e
    case m :: e                  => m :: innerUpdateMemory(x, v, e)
  }

  def run(c : Command, e : List[Map[String, Value]]) : Value = executeCommand(c, e, Nil)

  def executeCommand(c : Command, env : List[Map[String, Value]], mem : List[Map[String, Value]]) : Value =
    c match {
      case Ret(e) => ExprCompiler.run(e, env)
      case Bind(x, e, m) => {
        val Action(m2, closure) = ExprCompiler.run(e, env)
        val v = executeCommand(m2, closure :: env, mem)
        executeCommand(m, Map(x -> v) :: env, mem)
      }
      //Guarenteed to be there by the typechecker
      case Get(x)          => getBinding(mem, x)
      case SetCmd(x, e, m) => executeCommand(m, env, updateMemory(x, ExprCompiler.run(e, env), mem))
      case Decl(x, e, m)   => executeCommand(m, env, Map(x -> ExprCompiler.run(e, env)) :: mem)
    }

}