package compiler

import model.{SetCmd, Ret, Get, Decl, Command, Bind}

object CommandCompiler {

  sealed abstract class CmdStack(name : String) {
    override def toString : String = name
  }

  def getBinding(e : List[(String, Value)], x : String) : Value = e match {
    case Nil                   => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case (y, v) :: e if y == x => v
    case (y, v) :: e           => getBinding(e, x)
  }

  //Update the outermost stack-bound x
  private def updateMemory(x : String, v : Value, m : List[(String, Value)]) : List[(String, Value)] = m match {
    case Nil                    => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case (y, vv) :: e if y == x => (x -> v) :: e
    case (y, vv) :: e           => (y, vv) :: updateMemory(x, v, e)
  }

  def run(c : Command, e : List[Map[String, Value]], subdefs : List[ExprOpcode]) : Value = executeCommand(c, e, Nil, subdefs)

  def executeCommand(c : Command, env : List[Map[String, Value]], mem : List[(String, Value)], subdefs : List[ExprOpcode]) : Value =
    c match {
      case Ret(e)          => ExprCompiler.run(e, env, subdefs)
      case Get(x)          => getBinding(mem, x)
      case SetCmd(x, e, m) => executeCommand(m, env, updateMemory(x, ExprCompiler.run(e, env, subdefs), mem), subdefs)
      case Decl(x, e, m)   => executeCommand(m, env, (x -> ExprCompiler.run(e, env, subdefs)) :: mem, subdefs)
      case Bind(x, e, m) => {
        val Action(m2, closure) = ExprCompiler.run(e, env, subdefs)
        val v = executeCommand(m2, closure :: env, mem, subdefs)
        executeCommand(m, Map(x -> v) :: env, mem, subdefs)
      }
    }

}