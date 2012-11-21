package reduct

import model.{ Value, SetCmd, Ret, Get, Decl, Command, Bind, Action }

object CommandEvaluator {

  sealed abstract class Target
  case class Execute(c : Command) extends Target
  case class Return(v : Value) extends Target

  //All these are init'd to null, because they are manually set in each pass
  //Conceptually, this is a tail-recursive state-machine; for efficiency reasons we actually modify vars, but it's not strictly necessary
  private var target : Target = null //The command being executed or the value being returned
  private var stack : List[CmdStack] = null //The parts of the expression whose evaluation has been deferred
  private var env : List[Map[String, Value]] = null //The stack of variable-binding frames
  private var mem : List[Map[String, Value]] = null //The block-structured "memory"
  
  private def innerGetBinding(e : List[Map[String, Value]], x : String) : Value = e match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m(x)
    case m :: e                  => innerGetBinding(e, x)
  }

  //Update the outermost stack-bound x
  private def updateMemory(x : String, v : Value) = mem = innerUpdateMemory(x, v, mem)
  private def innerUpdateMemory(x : String, v : Value, m : List[Map[String, Value]]) : List[Map[String, Value]] = m match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m + (x -> v) :: e
    case m :: e                  => m :: innerUpdateMemory(x, v, e)
  }

  private def push(s : CmdStack) : Unit = stack = s :: stack

  private def pop : CmdStack = stack match {
    case Nil => throw new Exception("Should have aborted the command driver loop!") //This is the escape case
    case s :: stk => {
      stack = stk
      s
    }
  }
  
  //Ensure that all pushes are matched with pops
  private def pushMem(block : Map[String, Value]) : Unit = {
    mem = block :: mem
    push(PopBlock)
  }

  def run(c : Command, e : List[Map[String, Value]]) : Value = {
    env = e
    stack = Nil
    mem = Nil
    target = Execute(c)
    
    while (!(target.isInstanceOf[Return] && stack.isEmpty)) {
      execute
    }
    
    target.asInstanceOf[Return].v
  }

  private def execute : Unit = target match {
    case Execute(c) => c match {
      case Ret(e) => target = Return(ExprEvaluator.run(e, env))
      case Bind(x, e, m) => {
        val v = ExprEvaluator.run(e, env)
        v match {
          case Action(m2, closure) => {
            env = closure :: env
            push(CmdStackBind(x, m))
            target = Execute(m2)
          }
          case v => throw new Exception("Attempt to bind a non-action " + v)
        }
      }
      //Guarenteed to be there by the typechecker
      case Get(x)          => target = Return(innerGetBinding(mem, x))
      case SetCmd(x, e, m) => {
        updateMemory(x, ExprEvaluator.run(e, env))
        target = Execute(m)
      }
      case Decl(x, e, m)   => {
        pushMem(Map(x -> ExprEvaluator.run(e, env)))
        target = Execute(m)
      }
    }
    case Return(v) => pop match {
      case PopBlock => mem = mem.tail //Safe to pull out tail because the only change to mem's blocks-discipline is pushing along with a pop command
      case CmdStackBind(x, m) => {
        env = Map(x -> v) :: env
        target = Execute(m)
      }
    }
  }

}