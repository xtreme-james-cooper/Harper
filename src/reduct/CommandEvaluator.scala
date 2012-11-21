package reduct

import model.{Value, SetCmd, Ret, Get, Decl, Command, Bind, Action}

object CommandEvaluator {

  sealed abstract class CommandTarget
  case class Execute(c : Command) extends CommandTarget
  case class Return(v : Value) extends CommandTarget

  private def innerGetBinding(e : List[Map[String, Value]], x : String) : Value = e match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m(x)
    case m :: e                  => innerGetBinding(e, x)
  }

  //Update the outermost stack-bound x
  private def updateMemory(x : String, v : Value, mem : List[Map[String, Value]]) : List[Map[String, Value]] = mem match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m + (x -> v) :: e
    case m :: e                  => m :: updateMemory(x, v, e)
  }
  
  def run(c : Command, envv : List[Map[String, Value]]) : Value =
    execute(Execute(c), Nil, envv, Nil)._1

  //we can safely use the same env variable as Exprs do because Expr evaluation always pushes and pops in sync

  private def execute(c : CommandTarget, mem : List[Map[String, Value]],
                     envv : List[Map[String, Value]], stk : List[CmdStack]) : (Value, List[Map[String, Value]]) = c match {
    case Execute(c) => c match {
      case Ret(e) => execute(Return(ExprEvaluator.run(e, envv)), mem, envv, stk)
      case Bind(x, e, m) => {
        val v = ExprEvaluator.run(e, envv)
        v match {
          case Action(m2, closure) => execute(Execute(m2), mem, closure :: envv, CmdStackBind(x, m) :: stk)
          case _                   => throw new Exception("Attempt to bind a non-action " + v)
        }
      }
      //Guarenteed to be there by the typechecker
      case Get(x)          => execute(Return(innerGetBinding(mem, x)), mem, envv, stk)
      case SetCmd(x, e, m) => execute(Execute(m), updateMemory(x, ExprEvaluator.run(e, envv), mem), envv, stk)
      case Decl(x, e, m)   => execute(Execute(m), Map(x -> ExprEvaluator.run(e, envv)) :: mem, envv, PopBlock :: stk)
    }
    case Return(v) => stk match {
      case Nil                     => (v, mem)
      //Safe to pull out tail because the only change to mem's blocks-discipline is pushing along with a pop command
      case PopBlock :: s           => execute(Return(v), mem.tail, envv, s)
      case CmdStackBind(x, m) :: s => execute(Execute(m), mem, Map(x -> v) :: envv, s)
    }
  }


}