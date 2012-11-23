package compiler

import model.{ ZVal, Z, Var, Value, Unfold, TypeLam, TypeApp, TryCatch, TrivVal, Triv, ThrowEx, SVal, S, RecursiveLamVal, PairVal, PairEx, Match, LamVal, Lam, InRVal, InR, InLVal, InL, FoldVal, Fold, Fix, Expr, ExceptionValue, CommandExp, App, Action }

object ExprCompiler {

  type Env = List[Map[String, Value]] //Not V, specifically Value

  //All these are init'd to null, because they are manually set in each pass
  //Conceptually, this is a tail-recursive state-machine; for efficiency reasons we actually modify vars, but it's not strictly necessary
  var target : Target = null //The expression being evaluated, the value being returned, or the Exception being thrown
  var stack : List[ExprStack] = null //The parts of the expression whose evaluation has been deferred
  private var env : Env = null //The stack of variable-binding frames

  def push(s : ExprStack) : Unit = stack = s :: stack

  def getBinding(e : Env, x : String) : Value = e match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m(x)
    case m :: e                  => getBinding(e, x)
  }

  //Ensure that all pushes are matched with pops
  private def pushEnv(e : Map[String, Value]) : Unit = {
    env = e :: env
    push(PopFrame)
  }

  //Crush the env down into a single stack frame for use as a closure
  private def flattenEnv : Map[String, Value] = env.foldRight(Map[String, Value]())({ case (m1, m2) => m2 ++ m1 })

  def run(e : Expr, m : List[Map[String, Value]]) : Value = {
    env = m
    target = Eval(e)
    stack = Nil

    doEval
  }

  def doEval : Value = target match {
    case Eval(e) => e match {
      case Var(x) => {
        target = Return(getBinding(env, x))
        doEval
      }
      case Z => {
        target = Return(ZVal)
        doEval
      }
      case S(n) => {
        target = Eval(n)
        push(StackS)
        doEval
      }
      case Lam(v, t, e) => {
        target = Return(LamVal(v, e, flattenEnv))
        doEval
      }
      case App(e1, e2) => {
        target = Eval(e1)
        push(StackLam(e2))
        doEval
      }
      case Fix(v, Lam(x, t2, e)) => {
        pushEnv(Map(v -> RecursiveLamVal(v, x, e, flattenEnv)))
        target = Eval(Lam(x, t2, e))
        doEval
      }
      case Fix(v, e) => {
        target = Eval(e)
        doEval
      }
      case Triv => {
        target = Return(TrivVal)
        doEval
      }
      case PairEx(e1, e2) => {
        target = Eval(e1)
        push(StackLPair(e2))
        doEval
      }
      case InL(e) => {
        target = Eval(e)
        push(StackInL)
        doEval
      }
      case InR(e) => {
        target = Eval(e)
        push(StackInR)
        doEval
      }
      case Match(e, rs) => {
        target = Eval(e)
        push(StackCase(rs))
        doEval
      }
      case Fold(mu, t, e) => {
        target = Eval(e)
        push(StackFold)
        doEval
      }
      case Unfold(e) => {
        target = Eval(e)
        push(StackUnfold)
        doEval
      }
      case TypeLam(t, e) => {
        target = Eval(e)
        doEval
      }
      case TypeApp(e, t) => {
        target = Eval(e)
        doEval
      }
      case ThrowEx(s) => {
        target = Throw(s)
        doEval
      }
      case TryCatch(e1, e2) => {
        target = Eval(e1)
        push(StackHandler(e2))
        doEval
      }
      case CommandExp(c) => {
        target = Return(Action(c, flattenEnv))
        doEval
      }
    }
    case Return(v) => stack match {
      case Nil => v
      case StackS :: stk => {
        target = Return(SVal(v))
        stack = stk
        doEval
      }
      case StackLam(e2) :: stk => {
        target = Eval(e2)
        stack = stk
        push(StackArg(v))
        doEval
      }
      case StackArg(LamVal(x, e, clos)) :: stk => {
        pushEnv(clos + (x -> v))
        stack = stk
        target = Eval(e)
        doEval
      }
      case StackArg(v1) :: stk => throw new Exception("Application of a non-function : " + v1) //Typechecker should have caught this
      case StackLPair(e2) :: stk => {
        target = Eval(e2)
        stack = stk
        push(StackRPair(v))
        doEval
      }
      case StackRPair(v1) :: stk => {
        target = Return(PairVal(v1, v))
        stack = stk
        doEval
      }
      case StackInL :: stk => {
        target = Return(InLVal(v))
        stack = stk
        doEval
      }
      case StackInR :: stk => {
        target = Return(InRVal(v))
        stack = stk
        doEval
      }
      case StackCase(rs) :: stk => {
        val (e, bind) = PatternCompiler.run(v, rs)
        pushEnv(bind)
        target = Eval(e)
        stack = stk
        doEval
      }
      case StackFold :: stk => {
        target = Return(FoldVal(v))
        stack = stk
        doEval
      }
      case StackUnfold :: stk => v match {
        case FoldVal(v) => {
          target = Return(v)
          stack = stk
          doEval
        }
        case v => throw new Exception("Attempt to unfold a non-recursive value " + v) //typechecker should catch
      }
      case StackHandler(e2) :: stk => {
        stack = stk //if a value is returned, skip the handler
        doEval
      }
      case PopFrame :: stk => {
        env = env.tail //'tail' is safe, pops are added only with a frame
        stack = stk
        doEval
      }
    }
    case Throw(s) => stack match {
      case Nil => ExceptionValue(s)
      case StackHandler(e2) :: stk => {
        target = Eval(e2)
        stack = stk
        doEval
      }
      case _ :: stk => {
        stack = stk //if an exception is being thrown, pop stack
        doEval
      }
    }
  }

}