package compiler

import model.{ ZVal, Z, Var, Value, Unfold, TypeLam, TypeApp, TryCatch, TrivVal, Triv, ThrowEx, SVal, S, RecursiveLamVal, PairVal, PairEx, Match, LamVal, Lam, InRVal, InR, InLVal, InL, FoldVal, Fold, Fix, Expr, ExceptionValue, CommandExp, App, Action }

object ExprCompiler {

  type Env = List[Map[String, Value]] //Not V, specifically Value

  def getBinding(e : Env, x : String) : Value = e match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m(x)
    case m :: e                  => getBinding(e, x)
  }

  //Crush the env down into a single stack frame for use as a closure
  private def flatten(env : Env) : Map[String, Value] = env.foldRight(Map[String, Value]())({ case (m1, m2) => m2 ++ m1 })

  def run(e : Expr, m : List[Map[String, Value]]) : Value = doEval(Eval(e), m, Nil)

  def doEval(target : Target, env : Env, stack : List[ExprStack]) : Value = target match {
    case Eval(e) => e match {
      case Var(x)                => doEval(Return(getBinding(env, x)), env, stack)
      case Z                     => doEval(Return(ZVal), env, stack)
      case S(n)                  => doEval(Eval(n), env, StackS :: stack)
      case Lam(v, t, e)          => doEval(Return(LamVal(v, e, flatten(env))), env, stack)
      case App(e1, e2)           => doEval(Eval(e1), env, StackLam(e2) :: stack)
      case Fix(v, Lam(x, t2, e)) => doEval(Eval(Lam(x, t2, e)), Map(v -> RecursiveLamVal(v, x, e, flatten(env))) :: env, PopFrame :: stack)
      case Fix(v, e)             => doEval(Eval(e), env, stack)
      case Triv                  => doEval(Return(TrivVal), env, stack)
      case PairEx(e1, e2)        => doEval(Eval(e1), env, StackLPair(e2) :: stack)
      case InL(e)                => doEval(Eval(e), env, StackInL :: stack)
      case InR(e)                => doEval(Eval(e), env, StackInR :: stack)
      case Match(e, rs)          => doEval(Eval(e), env, StackCase(rs) :: stack)
      case Fold(mu, t, e)        => doEval(Eval(e), env, StackFold :: stack)
      case Unfold(e)             => doEval(Eval(e), env, StackUnfold :: stack)
      case TypeLam(t, e)         => doEval(Eval(e), env, stack)
      case TypeApp(e, t)         => doEval(Eval(e), env, stack)
      case ThrowEx(s)            => doEval(Throw(s), env, stack)
      case TryCatch(e1, e2)      => doEval(Eval(e1), env, StackHandler(e2) :: stack)
      case CommandExp(c)         => doEval(Return(Action(c, flatten(env))), env, stack)
    }
    case Return(v) => stack match {
      case Nil                                 => v
      case StackS :: stk                       => doEval(Return(SVal(v)), env, stk)
      case StackLam(e2) :: stk                 => doEval(Eval(e2), env, StackArg(v) :: stk)
      case StackArg(LamVal(x, e, clos)) :: stk => doEval(Eval(e), clos + (x -> v) :: env, PopFrame :: stk)
      case StackArg(v1) :: stk                 => throw new Exception("Application of a non-function : " + v1) //Typechecker should have caught this
      case StackLPair(e2) :: stk               => doEval(Eval(e2), env, StackRPair(v) :: stk)
      case StackRPair(v1) :: stk               => doEval(Return(PairVal(v1, v)), env, stk)
      case StackInL :: stk                     => doEval(Return(InLVal(v)), env, stk)
      case StackInR :: stk                     => doEval(Return(InRVal(v)), env, stk)
      case StackCase(rs) :: stk => {
        val (e, bind) = PatternCompiler.run(v, rs)
        doEval(Eval(e), bind :: env, PopFrame :: stk)
      }
      case StackFold :: stk => doEval(Return(FoldVal(v)), env, stk)
      case StackUnfold :: stk => v match {
        case FoldVal(v) => doEval(Return(v), env, stk)
        case v          => throw new Exception("Attempt to unfold a non-recursive value " + v) //typechecker should catch
      }
      case StackHandler(e2) :: stk => doEval(target, env, stk)
      case PopFrame :: stk         => doEval(target, env.tail, stk)
    }
    case Throw(s) => stack match {
      case Nil                     => ExceptionValue(s)
      case StackHandler(e2) :: stk => doEval(Eval(e2), env, stk)
      case _ :: stk                => doEval(target, env, stk)
    }
  }

}