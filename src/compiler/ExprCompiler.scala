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
    case Return(v) => stack match {
      case Nil => exval match {
        case None    => v
        case Some(s) => ExceptionValue(exval.get)
      }
      case StackS :: stk       => doEval(if (exval.isEmpty) Return(SVal(v)) else target, exval, env, stk)
      case StackLam(e2) :: stk => doEval(if (exval.isEmpty) Eval(e2) else target, exval, env, StackArg(v) :: stk)
      case StackArg(v1) :: stk =>
        if (exval.isDefined) doEval(target, exval, env, stk)
        else v1 match {
          case LamVal(x, e, clos) => doEval(Eval(e), exval, clos + (x -> v) :: env, PopFrame :: stk)
          case _                  => throw new Exception("Application of a non-function : " + v1)
        }
      case StackLPair(e2) :: stk => doEval(if (exval.isEmpty) Eval(e2) else target, exval, env, StackRPair(v) :: stk)
      case StackRPair(v1) :: stk => doEval(if (exval.isEmpty) Return(PairVal(v1, v)) else target, exval, env, stk)
      case StackInL :: stk       => doEval(if (exval.isEmpty) Return(InLVal(v)) else target, exval, env, stk)
      case StackInR :: stk       => doEval(if (exval.isEmpty) Return(InRVal(v)) else target, exval, env, stk)
      case StackCase(rs) :: stk => if (exval.isEmpty) {
        val (e, bind) = PatternCompiler.run(v, rs)
        doEval(Eval(e), exval, bind :: env, PopFrame :: stk)
      } else
        doEval(target, exval, env, stk)
      case StackFold :: stk        => doEval(if (exval.isEmpty) Return(FoldVal(v)) else target, exval, env, stk)
      case StackUnfold :: stk      => doEval(if (exval.isEmpty) Return(v.asInstanceOf[FoldVal].v) else target, exval, env, stk)
      case StackHandler(e2) :: stk => doEval(if (exval.isEmpty) target else Eval(e2), None, env, stk)
      case PopFrame :: stk         => doEval(target, exval, env.tail, stk)
    }
  }

}