package reduct

import model.{
  ZVal,
  Z,
  Var,
  Value,
  Unfold,
  TypeLam,
  TypeApp,
  TryCatch,
  TrivVal,
  Triv,
  ThrowEx,
  SVal,
  S,
  Rule,
  RecursiveLamVal,
  PairVal,
  PairEx,
  Match,
  LamVal,
  Lam,
  InRVal,
  InR,
  InLVal,
  InL,
  FoldVal,
  Fold,
  Fix,
  Expr,
  ExceptionValue,
  CommandExp,
  App,
  Action
}

object ExprEvaluator extends Evaluator[Stack, Expr, Value] {

  //All these are init'd to null, because they are manually set in each pass
  //Conceptually, this is a tail-recursive state-machine; for efficiency reasons we actually modify vars, but it's not strictly necessary
  private var env : List[Map[String, Value]] = null //The stack of variable-binding frames

  //Ensure that all pushes are matched with pops
  private def pushEnv(e : Map[String, Value]) : Unit = {
    env = e :: env
    push(PopFrame)
  }

  private def getBinding(x : String) : Value = innerGetBinding(env, x)
  private def innerGetBinding(e : List[Map[String, Value]], x : String) : Value = e match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m(x)
    case m :: e                  => innerGetBinding(e, x)
  }

  //Crush the env down into a single stack frame for use as a closure
  private def flattenEnv : Map[String, Value] = env.foldRight(Map[String, Value]())({ case (m1, m2) => m2 ++ m1 })

  def run(e : Expr, m : List[Map[String, Value]]) : Value = {
    target = Eval(e)
    env = m
    stack = Nil

    loop
    
    target match {
      case Return(v) => v
      case Throw(s)  => ExceptionValue(s)
      case Eval(e)   => throw new Exception("returning with evaluation still to be done?")
    }
  }

  override def evalStep(e : Expr) : Unit = e match {
    case Var(x) => target = Return(getBinding(x))
    case Z      => target = Return(ZVal)
    case S(n) => {
      target = Eval(n)
      push(StackS)
    }
    case Lam(v, t, e) => target = Return(LamVal(v, e, flattenEnv))
    case App(e1, e2) => {
      target = Eval(e1)
      push(StackLam(e2))
    }
    case Fix(v, Lam(x, t2, e)) => {
      pushEnv(Map(v -> RecursiveLamVal(v, x, e, flattenEnv)))
      target = Eval(Lam(x, t2, e))
    }
    case Fix(v, e) => target = Eval(e) //this will explode on CAFs (eg, recursive non-functions) so don't write them
    case Triv      => target = Return(TrivVal)
    case PairEx(e1, e2) => {
      target = Eval(e1)
      push(StackLPair(e2))
    }
    case InL(e) => {
      target = Eval(e)
      push(StackInL)
    }
    case InR(e) => {
      target = Eval(e)
      push(StackInR)
    }
    case Match(e, rs) => {
      target = Eval(e)
      push(StackCase(rs))
    }
    case Fold(mu, t, e) => {
      target = Eval(e)
      push(StackFold)
    }
    case Unfold(e) => {
      target = Eval(e)
      push(StackUnfold)
    }
    case TypeLam(t, e) => target = Eval(e) //Ignore types
    case TypeApp(e, t) => target = Eval(e) //Ignore types
    case ThrowEx(s)    => target = Throw(s)
    case TryCatch(e1, e2) => {
      target = Eval(e1)
      push(StackHandler(e2))
    }
    case CommandExp(c) => target = Return(Action(c, flattenEnv))
  }

  override def returnStep(v : Value, s : Stack) : Unit = s match {
    case StackS => target = Return(SVal(v))
    case StackLam(e2) => {
      target = Eval(e2)
      push(StackArg(v))
    }
    case StackArg(LamVal(x, e, clos)) => {
      pushEnv(clos + (x -> v))
      target = Eval(e)
    }
    case StackArg(v1) => throw new Exception("Application of a non-function : " + v1) //Typechecker should have caught this
    case StackLPair(e2) => {
      target = Eval(e2)
      push(StackRPair(v))
    }
    case StackRPair(v1) => target = Return(PairVal(v1, v))
    case StackInL       => target = Return(InLVal(v))
    case StackInR       => target = Return(InRVal(v))
    case StackCase(Nil) => throw new Exception("Empty set of rules?")
    case StackCase(Rule(p, b) :: rs) => {
      val (e, bind) = PatternEvaluator.run(v, p, b, rs)
      pushEnv(bind)
      target = Eval(e)
    }
    case StackFold => target = Return(FoldVal(v))
    case StackUnfold => v match {
      case FoldVal(v) => target = Return(v)
      case v          => throw new Exception("Attempt to unfold a non-recursive value " + v) //typechecker should catch
    }
    case StackHandler(e2) => () //if a value is returned, skip the handler
    case PopFrame         => env = env.tail //'tail' is safe, pops are added only with a frame
  }

  override def throwStep(s : String) : Unit = pop match {
    case StackHandler(e2) => target = Eval(e2)
    case _                => () //if an exception is being thrown, pop stack
  }

}