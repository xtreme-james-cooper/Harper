package reduct

abstract class Evaluator[Stk, E, V] {

  //All these are init'd to null, because they are manually set in each pass
  //Conceptually, this is a tail-recursive state-machine; for efficiency reasons we actually modify vars, but it's not strictly necessary
  var target : Target[E, V] = null //The expression being evaluated, the value being returned, or the Exception being thrown
  var stack : List[Stk] = null //The parts of the expression whose evaluation has been deferred

  def push(s : Stk) : Unit = stack = s :: stack

  def pop : Stk = stack match {
    case Nil => throw new Exception("Should have aborted the driver loop!") //This is the escape case
    case s :: stk => {
      stack = stk
      s
    }
  }

  def loop : Unit = {
    while (target.isInstanceOf[Eval[E, V]] || !stack.isEmpty) {
      target match {
        case Eval(e)   => evalStep(e)
        case Return(v) => returnStep(v, pop)
        case Throw(s)  => throwStep(s)
      }
    }
  }

  def evalStep(e : E) : Unit
  def returnStep(v : V, s : Stk) : Unit
  def throwStep(s : String) : Unit

}