package compiler

import model.{ ZVal, Z, Var, Value, Unfold, TypeLam, TypeApp, TryCatch, TrivVal, Triv, ThrowEx, SVal, S, RecursiveLamVal, PairVal, PairEx, Match, LamVal, Lam, InRVal, InR, InLVal, InL, FoldVal, Fold, Fix, Expr, ExceptionValue, CommandExp, App, Action }

object ExprCompiler {

  sealed abstract class Target
  case class Eval(e : Expr) extends Target
  case class Return(v : Value) extends Target

  type Env = List[Map[String, Value]] //Not V, specifically Value

  def getBinding(e : Env, x : String) : Value = e match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m(x)
    case m :: e                  => getBinding(e, x)
  }

  //Crush the env down into a single stack frame for use as a closure
  private def flatten(env : Env) : Map[String, Value] = env.foldRight(Map[String, Value]())({ case (m1, m2) => m2 ++ m1 })

  def run(e : Expr, m : List[Map[String, Value]]) : Value = doEval(Eval(e), None, m, Nil)

  def doEval(target : Target, exval : Option[String], env : Env, stack : List[ExprStack]) : Value = target match {
    case Eval(e) => e match {
      case Var(x)                => doEval(Return(getBinding(env, x)), None, env, stack)
      case Z                     => doEval(Return(ZVal), None, env, stack)
      case S(n)                  => doEval(Eval(n), None, env, StackS :: stack)
      case Lam(v, t, e)          => doEval(Return(LamVal(v, e, flatten(env))), None, env, stack)
      case App(e1, e2)           => doEval(Eval(e1), None, env, StackLam(e2) :: stack)
      case Fix(v, Lam(x, t2, e)) => doEval(Eval(Lam(x, t2, e)), None, Map(v -> RecursiveLamVal(v, x, e, flatten(env))) :: env, PopFrame :: stack)
      case Fix(v, e)             => doEval(Eval(e), None, env, stack)
      case Triv                  => doEval(Return(TrivVal), None, env, stack)
      case PairEx(e1, e2)        => doEval(Eval(e1), None, env, StackLPair(e2) :: stack)
      case InL(e)                => doEval(Eval(e), None, env, StackInL :: stack)
      case InR(e)                => doEval(Eval(e), None, env, StackInR :: stack)
      case Match(e, rs)          => doEval(Eval(e), None, env, StackCase(rs) :: stack)
      case Fold(mu, t, e)        => doEval(Eval(e), None, env, StackFold :: stack)
      case Unfold(e)             => doEval(Eval(e), None, env, StackUnfold :: stack)
      case TypeLam(t, e)         => doEval(Eval(e), None, env, stack)
      case TypeApp(e, t)         => doEval(Eval(e), None, env, stack)
      case ThrowEx(s)            => doEval(Return(TrivVal), Some(s), env, stack)
      case TryCatch(e1, e2)      => doEval(Eval(e1), None, env, StackHandler(e2) :: stack)
      case CommandExp(c)         => doEval(Return(Action(c, flatten(env))), None, env, stack)
    }
    case Return(v) =>
      if (exval.isEmpty)
        stack match {
          case Nil                                 => v
          case StackS :: stk                       => doEval(Return(SVal(v)), None, env, stk)
          case StackLam(e2) :: stk                 => doEval(Eval(e2), None, env, StackArg(v) :: stk)
          case StackArg(LamVal(x, e, clos)) :: stk => doEval(Eval(e), None, clos + (x -> v) :: env, PopFrame :: stk)
          case StackArg(v1) :: stk                 => throw new Exception("Application of a non-function : " + v1) //Typechecker should have caught this
          case StackLPair(e2) :: stk               => doEval(Eval(e2), None, env, StackRPair(v) :: stk)
          case StackRPair(v1) :: stk               => doEval(Return(PairVal(v1, v)), None, env, stk)
          case StackInL :: stk                     => doEval(Return(InLVal(v)), None, env, stk)
          case StackInR :: stk                     => doEval(Return(InRVal(v)), None, env, stk)
          case StackCase(rs) :: stk => {
            val (e, bind) = PatternCompiler.run(v, rs)
            doEval(Eval(e), None, bind :: env, PopFrame :: stk)
          }
          case StackFold :: stk => doEval(Return(FoldVal(v)), None, env, stk)
          case StackUnfold :: stk => v match {
            case FoldVal(v) => doEval(Return(v), None, env, stk)
            case v          => throw new Exception("Attempt to unfold a non-recursive value " + v) //typechecker should catch
          }
          case StackHandler(e2) :: stk => doEval(target, None, env, stk)
          case PopFrame :: stk         => doEval(target, None, env.tail, stk)
        }
      else stack match {
        case Nil                     => ExceptionValue(exval.get)
        case StackHandler(e2) :: stk => doEval(Eval(e2), None, env, stk)
        case _ :: stk                => doEval(target, exval, env, stk)
      }
  }

}