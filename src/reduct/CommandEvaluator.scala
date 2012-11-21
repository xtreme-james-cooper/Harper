package reduct

import model.{ Value, SetCmd, Ret, Get, Decl, Command, Bind, Action }

object CommandEvaluator extends Evaluator[CmdStack, Command, Value] {

  //All these are init'd to null, because they are manually set in each pass
  //Conceptually, this is a tail-recursive state-machine; for efficiency reasons we actually modify vars, but it's not strictly necessary
  private var env : Env = null //The stack of variable-binding frames
  private var mem : Env = null //The block-structured "memory"

  //Update the outermost stack-bound x
  private def updateMemory(x : String, v : Value) = mem = innerUpdateMemory(x, v, mem)
  private def innerUpdateMemory(x : String, v : Value, m : List[Map[String, Value]]) : List[Map[String, Value]] = m match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m + (x -> v) :: e
    case m :: e                  => m :: innerUpdateMemory(x, v, e)
  }

  //Ensure that all pushes are matched with pops
  private def pushMem(block : Map[String, Value]) : Unit = {
    mem = block :: mem
    push(PopBlock)
  }

  def run(c : Command, e : List[Map[String, Value]]) : Value = {
    env = e
    mem = Nil

    loop(c)

    target.asInstanceOf[Return[Command, Value]].v
  }

  override def evalStep(c : Command) : Unit = c match {
    case Ret(e) => target = Return(ExprEvaluator.run(e, env))
    case Bind(x, e, m) => ExprEvaluator.run(e, env) match {
      case Action(m2, closure) => {
        env = closure :: env
        push(CmdStackBind(x, m))
        target = Eval(m2)
      }
      case v => throw new Exception("Attempt to bind a non-action " + v)
    }
    //Guarenteed to be there by the typechecker
    case Get(x) => target = Return(getBinding(mem, x))
    case SetCmd(x, e, m) => {
      updateMemory(x, ExprEvaluator.run(e, env))
      target = Eval(m)
    }
    case Decl(x, e, m) => {
      pushMem(Map(x -> ExprEvaluator.run(e, env)))
      target = Eval(m)
    }
  }

  override def returnStep(v : Value, s : CmdStack) : Unit = s match {
    case PopBlock => mem = mem.tail //Safe to pull out tail because the only change to mem's blocks-discipline is pushing along with a pop command
    case CmdStackBind(x, m) => {
      env = Map(x -> v) :: env
      target = Eval(m)
    }
  }

  override def throwStep(s : String) : Unit =
    throw new Exception("Unexpected throw " + s + " in command executor") //Should not happen

}