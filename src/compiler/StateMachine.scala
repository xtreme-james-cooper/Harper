package compiler

import model.{ ZPat, Z, WildPat, VarPat, Var, Unitt, Unfold, UncaughtException, TrivPat, Triv, TLam, TAp, SPat, S, Raise, ProjR, ProjL, Pattern, Pairr, PairPat, Match, Let, Lam, InRPat, InR, InLPat, InL, Fold, Fix, Expr, Catch, Ap, Abort }
import interpreter.Substitutor.subst

sealed abstract class State
case object EvalExpr extends State
case object ReturnExpr extends State
case object FailExpr extends State
case object EvalRules extends State
case object EvalMatch extends State
case object ReturnMatch extends State
case object FailMatch extends State

object StateMachine {

  private var state : State = null
  private var expr : Expr = null
  private var stack : List[Stack] = null
  private var rules : List[(Pattern, Expr)] = null
  private var comp : (Pattern, Expr) = null
  private var bind : Map[String, Expr] = null

  def eval(e : Expr) : Expr = {
    state = EvalExpr
    expr = e
    stack = Nil
    do {
      doStep
    } while (!stack.isEmpty)
    expr
  }

  private def doStep : Unit = state match {
    case EvalExpr    => evalExpr
    case ReturnExpr  => returnExpr
    case FailExpr    => failExpr
    case EvalRules   => evalRules
    case EvalMatch   => evalMatch
    case ReturnMatch => returnMatch
    case FailMatch   => failMatch
  }

  private def evalExpr : Unit = expr match {
    case Var(x) => throw new Exception("unsubstituted variable " + x)
    case Z      => returnExpr
    case S(e) => {
      expr = e
      stack = SStk :: stack
      evalExpr
    }
    case Lam(x, t, e) => returnExpr
    case Let(n, d, b) => {
      expr = d
      stack = LetStk(n, b) :: stack
      evalExpr
    }
    case Ap(e1, e2) => {
      expr = e1
      stack = ApStk(e2) :: stack
      evalExpr
    }
    case Fix(x, t, e) => {
      expr = subst(Map(x -> Fix(x, t, e)))(e)
      evalExpr
    }
    case Triv => returnExpr
    case Pairr(e1, e2) => {
      expr = e1
      stack = PairrStk(e2) :: stack
      evalExpr
    }
    case ProjL(e) => {
      expr = e
      stack = ProjLStk :: stack
      evalExpr
    }
    case ProjR(e) => {
      expr = e
      stack = ProjRStk :: stack
      evalExpr
    }
    case Abort(t, e) => {
      expr = e
      stack = AbortStk :: stack
      evalExpr
    }
    case InL(t, e) => {
      expr = e
      stack = InLStk :: stack
      evalExpr
    }
    case InR(t, e) => {
      expr = e
      stack = InRStk :: stack
      evalExpr
    }
    case Match(e, rs) => {
      expr = e
      stack = MatchStk(rs) :: stack
      evalExpr
    }
    case Fold(x, t, e) => {
      expr = e
      stack = FoldStk(x) :: stack
      evalExpr
    }
    case Unfold(e) => {
      expr = e
      stack = UnfoldStk :: stack
      evalExpr
    }
    case TLam(x, e) => {
      expr = e
      evalExpr
    }
    case TAp(e, t) => {
      expr = e
      evalExpr
    }
    case Raise(t) => failExpr
    case Catch(e1, e2) => {
      expr = e1
      stack = CatchStk(e2) :: stack
      evalExpr
    }
    case UncaughtException => failExpr
  }

  private def returnExpr : Unit = stack match {
    case Nil => ()
    case SStk :: ss => {
      expr = S(expr)
      stack = ss
      returnExpr
    }
    case LetStk(n, b) :: ss => {
      expr = subst(Map(n -> expr))(b)
      stack = ss
      evalExpr
    }
    case ApStk(e2 : Expr) :: ss => expr match {
      case Lam(x, t, b) => {
        expr = e2
        stack = Ap2Stk(x, b) :: ss
        evalExpr
      }
      case _ => throw new Exception("application of non-function " + expr)
    }
    case Ap2Stk(x, b) :: ss => {
      expr = subst(Map(x -> expr))(b)
      stack = ss
      evalExpr
    }
    case PairrStk(e2 : Expr) :: ss => {
      stack = Pairr2Stk(expr) :: ss
      expr = e2
      evalExpr
    }
    case Pairr2Stk(e1 : Expr) :: ss => {
      expr = Pairr(e1, expr)
      stack = ss
      returnExpr
    }
    case ProjLStk :: ss => expr match {
      case Pairr(e1, e2) => {
        expr = e1
        stack = ss
        returnExpr
      }
      case _ => throw new Exception("projL of non-pair " + expr)
    }
    case ProjRStk :: ss => expr match {
      case Pairr(e1, e2) => {
        expr = e2
        stack = ss
        returnExpr
      }
      case _ => throw new Exception("projR of non-pair " + expr)
    }
    case AbortStk :: ss => {
      expr = Abort(Unitt, expr)
      stack = ss
      returnExpr
    }
    case InLStk :: ss => {
      expr = InL(Unitt, expr)
      stack = ss
      returnExpr
    }
    case InRStk :: ss => {
      expr = InR(Unitt, expr)
      stack = ss
      returnExpr
    }
    case MatchStk(rs) :: ss => {
      stack = ss
      rules = rs
      evalRules
    }
    case FoldStk(x : String) :: ss => {
      expr = Fold(x, Unitt, expr)
      stack = ss
      returnExpr
    }
    case UnfoldStk :: ss => expr match {
      case Fold(x, t, e) => {
        expr = e
        stack = ss
        returnExpr
      }
      case _ => throw new Exception("unfold of non-fold " + expr)
    }
    case CatchStk(e2) :: ss => {
      stack = ss
      returnExpr
    }
    case PatStkRules(e, b, rs) :: ss => throw new Exception("pattern matching on stack during eval")
    case PairPatStk(p2, e2) :: ss    => throw new Exception("pattern matching on stack during eval")
    case Pair2PatStk(bind1) :: ss    => throw new Exception("pattern matching on stack during eval")
  }

  private def failExpr : Unit = stack match {
    case Nil => expr = UncaughtException
    case SStk :: ss => {
      stack = ss
      failExpr
    }
    case LetStk(n, b) :: ss => {
      stack = ss
      failExpr
    }
    case ApStk(e2 : Expr) :: ss => {
      stack = ss
      failExpr
    }
    case Ap2Stk(x, b) :: ss => {
      stack = ss
      failExpr
    }
    case PairrStk(e2 : Expr) :: ss => {
      stack = ss
      failExpr
    }
    case Pairr2Stk(e1 : Expr) :: ss => {
      stack = ss
      failExpr
    }
    case ProjLStk :: ss => {
      stack = ss
      failExpr
    }
    case ProjRStk :: ss => {
      stack = ss
      failExpr
    }
    case AbortStk :: ss => {
      stack = ss
      failExpr
    }
    case InLStk :: ss => {
      stack = ss
      failExpr
    }
    case InRStk :: ss => {
      stack = ss
      failExpr
    }
    case MatchStk(rs) :: ss => {
      stack = ss
      failExpr
    }
    case FoldStk(x : String) :: ss => {
      stack = ss
      failExpr
    }
    case UnfoldStk :: ss => {
      stack = ss
      failExpr
    }
    case CatchStk(e2) :: ss => {
      expr = e2
      stack = ss
      evalExpr
    }
    case PatStkRules(e, b, rs) :: ss => throw new Exception("pattern matching on stack during eval")
    case PairPatStk(p2, e2) :: ss    => throw new Exception("pattern matching on stack during eval")
    case Pair2PatStk(bind1) :: ss    => throw new Exception("pattern matching on stack during eval")
  }

  private def evalRules : Unit = rules match {
    case Nil => throw new Exception("no match found for " + expr)
    case (p, b) :: rs => {
      stack = PatStkRules(expr, b, rs) :: stack
      comp = (p, expr)
      evalMatch
    }
  }

  private def evalMatch : Unit = comp match {
    case (WildPat, _) => {
      bind = Map()
      returnMatch
    }
    case (VarPat(x), e) => {
      bind = Map(x -> e)
      returnMatch
    }
    case (TrivPat, Triv) => {
      bind = Map()
      returnMatch
    }
    case (PairPat(p1, p2), Pairr(e1, e2)) => {
      stack = PairPatStk(p2, e2) :: stack
      comp = (p1, e1)
      evalMatch
    }
    case (InLPat(p), InL(t, e)) => {
      comp = (p, e)
      evalMatch
    }
    case (InRPat(p), InR(t, e)) => {
      comp = (p, e)
      evalMatch
    }
    case (ZPat, Z) => {
      bind = Map()
      returnMatch
    }
    case (SPat(p), S(e)) => {
      comp = (p, e)
      evalMatch
    }
    case _ => failMatch
  }

  private def returnMatch : Unit = stack match {
    case PatStkRules(e, b, rs) :: ss => {
      expr = subst(bind)(b)
      stack = ss
      evalExpr
    }
    case PairPatStk(p2, e2) :: ss => {
      stack = Pair2PatStk(bind) :: ss
      comp = (p2, e2)
      evalMatch
    }
    case Pair2PatStk(bind1) :: ss => {
      stack = ss
      bind = bind1 ++ bind
      returnMatch
    }
    case _ => throw new Exception("no pattern rules on stack")
  }

  private def failMatch : Unit = stack match {
    case PatStkRules(e, b, rs) :: ss => {
      expr = e
      stack = ss
      rules = rs
      evalRules
    }
    case PairPatStk(p2, e2) :: ss => {
      stack = ss
      failMatch
    }
    case Pair2PatStk(bind1) :: ss => {
      stack = ss
      failMatch
    }
    case _ => throw new Exception("no pattern rules on stack")
  }

}