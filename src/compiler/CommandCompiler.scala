package compiler

import model.{ Value, SetCmd, Ret, Get, Decl, Command, Bind, Action }

object CommandCompiler {

  sealed abstract class Target
  case class Eval(e : Command) extends Target
  case class Return(v : Value) extends Target

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

  def run(c : Command, e : List[Map[String, Value]]) : Value = executeCommand(Eval(c), e, Nil, Nil)

  def executeCommand(target : Target, env : List[Map[String, Value]], mem : List[Map[String, Value]], stack : List[CmdStack]) : Value =
    target match {
      case Eval(e) => e match {
        case Ret(e) => executeCommand(Return(ExprCompiler.run(e, env)), env, mem, stack)
        case Bind(x, e, m) => ExprCompiler.run(e, env) match {
          case Action(m2, closure) => executeCommand(Eval(m2), closure :: env, mem, CmdStackBind(x, m) :: stack)
          case v => throw new Exception("Attempt to bind a non-action " + v)
        }
        //Guarenteed to be there by the typechecker
        case Get(x)          => executeCommand(Return(getBinding(mem, x)), env, mem, stack)
        case SetCmd(x, e, m) => executeCommand(Eval(m), env, updateMemory(x, ExprCompiler.run(e, env), mem), stack)
        case Decl(x, e, m) => executeCommand(Eval(m), env, Map(x -> ExprCompiler.run(e, env)) :: mem, PopBlock :: stack)
      }
      case Return(v) => stack match {
        case Nil => v
        case PopBlock :: stk => executeCommand(target, env, mem.tail, stk)
        case CmdStackBind(x, m) :: stk => executeCommand(Eval(m), Map(x -> v) :: env, mem, stk)
      }
    }

}