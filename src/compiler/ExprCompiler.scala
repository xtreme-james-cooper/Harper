package compiler

import model.{ ZVal, Z, Var, Value, Unfold, TypeLam, TypeApp, TryCatch, TrivVal, Triv, ThrowEx, SVal, S, Rule, RecursiveLamVal, PairVal, PairEx, Match, LamVal, Lam, InRVal, InR, InLVal, InL, FoldVal, Fold, Fix, Expr, ExceptionValue, CommandExp, App, Action }

object ExprCompiler {

  def getBinding(e : List[Map[String, Value]], x : String) : Value = e match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m(x)
    case m :: e                  => getBinding(e, x)
  }

  //Crush the env down into a single stack frame for use as a closure
  private def flatten(env : List[Map[String, Value]]) : Map[String, Value] = env.foldRight(Map[String, Value]())({ case (m1, m2) => m2 ++ m1 })

  def run(e : Expr, m : List[Map[String, Value]]) : Value = ExprCPU.run(compileExpr(e), m)

  def compileExpr(e0 : Expr) : List[ExprOpcode] = e0 match {
    case Var(x)           => List(RunExpr(e0), ExprExit)
    case Z                => List(RunExpr(e0), ExprExit)
    case S(n)             => List(RunExpr(e0), ExprExit)
    case Lam(v, t, e)     => List(RunExpr(e0), ExprExit)
    case App(e1, e2)      => List(RunExpr(e0), ExprExit)
    case Fix(v, e)        => List(RunExpr(e0), ExprExit)
    case Triv             => List(RunExpr(e0), ExprExit)
    case PairEx(e1, e2)   => List(RunExpr(e0), ExprExit)
    case InL(e)           => List(RunExpr(e0), ExprExit)
    case InR(e)           => List(RunExpr(e0), ExprExit)
    case Match(e, rs)     => List(RunExpr(e0), ExprExit)
    case Fold(mu, t, e)   => List(RunExpr(e0), ExprExit)
    case Unfold(e)        => List(RunExpr(e0), ExprExit)
    case TypeLam(t, e)    => List(RunExpr(e0), ExprExit)
    case TypeApp(e, t)    => List(RunExpr(e0), ExprExit)
    case ThrowEx(s)       => List(RunExpr(e0), ExprExit)
    case TryCatch(e1, e2) => List(RunExpr(e0), ExprExit)
    case CommandExp(c)    => List(RunExpr(e0), ExprExit)
  }

  def doEval(e : Expr, env : List[Map[String, Value]]) : Value = e match {
    case Var(x) => getBinding(env, x)
    case Z      => ZVal
    case S(n) => {
      val v = doEval(n, env)
      if (v.isInstanceOf[ExceptionValue])
        v
      else
        SVal(v)
    }
    case Lam(v, t, e) => LamVal(v, e, flatten(env))
    case App(e1, e2) => {
      val v1 = doEval(e1, env)
      if (v1.isInstanceOf[ExceptionValue])
        v1
      else {
        val v2 = doEval(e2, env)
        if (v2.isInstanceOf[ExceptionValue])
          v2
        else v1 match {
          case LamVal(x, e, clos) => doEval(e, clos + (x -> v2) :: env)
          case _                  => throw new Exception("Application of a non-function : " + v1) //Not possible by typecheck
        }
      }
    }
    case Fix(v, Lam(x, t2, e)) => doEval(Lam(x, t2, e), Map(v -> RecursiveLamVal(v, x, e, flatten(env))) :: env)
    case Fix(v, e)             => doEval(e, env) //this will explode on CAFs (eg, recursive non-functions) so don't write them
    case Triv                  => TrivVal
    case PairEx(e1, e2) => {
      val v1 = doEval(e1, env)
      if (v1.isInstanceOf[ExceptionValue])
        v1
      else {
        val v2 = doEval(e2, env)
        if (v2.isInstanceOf[ExceptionValue])
          v2
        else
          PairVal(v1, v2)
      }
    }
    case InL(e) => {
      val v = doEval(e, env)
      if (v.isInstanceOf[ExceptionValue])
        v
      else
        InLVal(v)
    }
    case InR(e) => {
      val v = doEval(e, env)
      if (v.isInstanceOf[ExceptionValue])
        v
      else
        InRVal(v)
    }
    case Match(e, rs) => {
      val v = doEval(e, env)
      if (v.isInstanceOf[ExceptionValue])
        v
      else {
        val (e, bind) = PatternCompiler.run(v, rs)
        doEval(e, bind :: env)
      }
    }
    case Fold(mu, t, e) => {
      val v = doEval(e, env)
      if (v.isInstanceOf[ExceptionValue])
        v
      else
        FoldVal(v)
    }
    case Unfold(e) => {
      val v = doEval(e, env)
      if (v.isInstanceOf[ExceptionValue])
        v
      else
        v.asInstanceOf[FoldVal].v
    }
    case TypeLam(t, e) => doEval(e, env)
    case TypeApp(e, t) => doEval(e, env)
    case ThrowEx(s)    => ExceptionValue(s)
    case TryCatch(e1, e2) => {
      val v = doEval(e1, env)
      if (v.isInstanceOf[ExceptionValue])
        doEval(e2, env)
      else
        v
    }
    case CommandExp(c) => Action(c, flatten(env))
  }

}