package compiler

import model.{ ZVal, Z, Var, Value, Unfold, TypeLam, TypeApp, TryCatch, TrivVal, Triv, ThrowEx, SVal, S, Rule, RecursiveLamVal, PairVal, PairEx, Match, LamVal, Lam, InRVal, InR, InLVal, InL, FoldVal, Fold, Fix, Expr, ExceptionValue, CommandExp, App, Action }

object ExprCompiler {

  var n : Int = 0

  def getBinding(e : List[Map[String, Value]], x : String) : Value = e match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m(x)
    case m :: e                  => getBinding(e, x)
  }

  //Crush the env down into a single stack frame for use as a closure
  def flatten(env : List[Map[String, Value]]) : Map[String, Value] = env.foldRight(Map[String, Value]())({ case (m1, m2) => m2 ++ m1 })

  def run(e : Expr, m : List[Map[String, Value]]) : Value = ExprCPU.run(compileExpr(e) ++ List(ExprExit), m)

  def compileExpr(e0 : Expr) : List[ExprOpcode] = e0 match {
    case Var(x) => List(RunExpr(e0))
    case Z      => List(ReturnOp(ZVal))
    case S(e) => {
      val exnLabel = "exnshortcut" + n
      n = n + 1
      compileExpr(e) ++ List(JIfExn(exnLabel), PushS, ExprLabel(exnLabel))
    }
    case Lam(v, t, e) => List(RunExpr(e0))
    case App(e1, e2)  => List(RunExpr(e0))
    case Fix(v, e)    => List(RunExpr(e0))
    case Triv         => List(ReturnOp(TrivVal))
    case PairEx(e1, e2) => {
      val exnLabel = "exnshortcut" + n
      n = n + 1
      compileExpr(e1) ++ List(JIfExn(exnLabel)) ++ compileExpr(e2) ++ List(JIfExn(exnLabel), PushPair, ExprLabel(exnLabel))
    }
    case InL(e) => {
      val exnLabel = "exnshortcut" + n
      n = n + 1
      compileExpr(e) ++ List(JIfExn(exnLabel), PushInL, ExprLabel(exnLabel))
    }
    case InR(e) => {
      val exnLabel = "exnshortcut" + n
      n = n + 1
      compileExpr(e) ++ List(JIfExn(exnLabel), PushInR, ExprLabel(exnLabel))
    }
    case Match(e, rs)     => List(RunExpr(e0))
    case Fold(mu, t, e)   => List(RunExpr(e0))
    case Unfold(e)        => List(RunExpr(e0))
    case TypeLam(t, e)    => compileExpr(e)
    case TypeApp(e, t)    => compileExpr(e)
    case ThrowEx(s)       => List(RunExpr(e0))
    case TryCatch(e1, e2) => List(RunExpr(e0))
    case CommandExp(c)    => List(RunExpr(e0))
  }

  def doEval(e : Expr, env : List[Map[String, Value]]) : Value = e match {
    case Var(x)       => getBinding(env, x)
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
    case ThrowEx(s) => ExceptionValue(s)
    case TryCatch(e1, e2) => {
      val v = doEval(e1, env)
      if (v.isInstanceOf[ExceptionValue])
        doEval(e2, env)
      else
        v
    }
    case CommandExp(c) => Action(c, flatten(env))

    case Triv          => TrivVal
    case TypeLam(t, e) => doEval(e, env)
    case TypeApp(e, t) => doEval(e, env)
    case Z             => ZVal
    case S(n) => {
      val v = doEval(n, env)
      if (v.isInstanceOf[ExceptionValue])
        v
      else
        SVal(v)
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

  }

}