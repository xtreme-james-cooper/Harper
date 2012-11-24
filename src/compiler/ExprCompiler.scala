package compiler

import model.{ Z, Var, Unfold, TypeLam, TypeApp, TryCatch, Triv, ThrowEx, S, PairEx, Match, Lam, InR, InL, Fold, Expr, CommandExp, App }
import model.Rule
import model.Pattern

object ExprCompiler {

  var n : Int = 0

  def getBinding(e : List[Map[String, Value]], x : String) : Value = e match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m(x)
    case m :: e                  => getBinding(e, x)
  }

  //Crush the env down into a single stack frame for use as a closure
  def flatten(env : List[Map[String, Value]]) : Map[String, Value] = env.foldRight(Map[String, Value]())({ case (m1, m2) => m2 ++ m1 })

  def run(e : Expr, m : List[Map[String, Value]], subdefs : List[ExprOpcode]) : Value = {
    val code = compileExpr(e) ++ List(ExprExit) ++ subdefs
    
//    for (i <- 0 until code.length) println(i + ": " + code(i))
    
    ExprCPU.run(code, m)
  }

  def compileExpr(e0 : Expr) : List[ExprOpcode] = e0 match {
    case Var(x) => List(DerefVar(x))
    case Z      => List(ReturnOp(ZVal))
    case S(e) => {
      val exnLabel = "exnshortcut" + n
      n = n + 1
      compileExpr(e) ++ List(JIfExn(exnLabel), PushS, ExprLabel(exnLabel))
    }
    case Lam(v, t, e) => {
      val procname = "proc" + n
      n = n + 1
      List(FlattenEnv, PushLam(v, procname)) ++ compileSubroutine(procname, e)
    }
    case App(e1, e2) => {
      val exnLabel = "exnshortcut" + n
      n = n + 1
      compileExpr(e2) ++ List(JIfExn(exnLabel)) ++ compileExpr(e1) ++ List(JIfExn(exnLabel)) ++ subroutineCall ++ List(ExprLabel(exnLabel))
    }
    case Triv      => List(ReturnOp(TrivVal))
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
    case Match(e, rs) => {
      val exnLabel = "exnshortcut" + n
      n = n + 1

      var bodies : List[ExprOpcode] = Nil
      var rules : List[(Pattern, String)] = Nil
      for (Rule(p, b) <- rs) {
        val subname = "matchbody" + n
        n = n + 1
        bodies = bodies ++ compileSubroutine(subname, b)
        rules = rules ++ List((p, subname))
      }

      compileExpr(e) ++ List(JIfExn(exnLabel)) ++ bodies ++ patSubroutineCall(rules) ++ List(ExprLabel(exnLabel))
    }
    case Fold(mu, t, e) => {
      val exnLabel = "exnshortcut" + n
      n = n + 1
      compileExpr(e) ++ List(JIfExn(exnLabel), PushFold, ExprLabel(exnLabel))
    }
    case Unfold(e) => {
      val exnLabel = "exnshortcut" + n
      n = n + 1
      compileExpr(e) ++ List(JIfExn(exnLabel), PopFold, ExprLabel(exnLabel))
    }
    case TypeLam(t, e) => compileExpr(e)
    case TypeApp(e, t) => compileExpr(e)
    case ThrowEx(s)    => List(ReturnOp(ExceptionValue(s)))
    case TryCatch(e1, e2) => {
      val exnLabel = "exnshortcut" + n
      n = n + 1
      compileExpr(e1) ++ List(JIfNExn(exnLabel)) ++ compileExpr(e2) ++ List(ExprLabel(exnLabel))
    }
    case CommandExp(c) => List(FlattenEnv, PushCommand(c))
  }

  def compileSubroutine(name : String, body : Expr) : List[ExprOpcode] = {
    val jump = "jump" + n
    n = n + 1
    List(ExprJump(jump), ExprLabel(name)) ++ compileExpr(body) ++ List(JumpReturn, ExprLabel(jump))
  }

  def subroutineCall : List[ExprOpcode] = {
    val returnLabel = "return" + n
    n = n + 1
    List(PushReturn(returnLabel), RunLambda, ExprLabel(returnLabel), PopEnv)
  }

  def patSubroutineCall(rules : List[(Pattern, String)]) : List[ExprOpcode] = {
    val returnLabel = "return" + n
    n = n + 1
    List(RunPat(rules), PushReturn(returnLabel), JumpPatBody, ExprLabel(returnLabel), PopEnv)
  }

}