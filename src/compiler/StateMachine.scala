package compiler

import model.{ ZPat, Z, WildPat, VarPat, Var, Unitt, Unfold, UncaughtException, TrivPat, Triv, TLam, TAp, SPat, S, Raise, ProjR, ProjL, Pattern, Pairr, PairPat, Match, Let, Lam, InRPat, InR, InLPat, InL, Fold, Fix, Expr, Catch, Ap, Abort }
import interpreter.Substitutor.subst

sealed abstract class State(val isTermination : Boolean)
case object EvalExpr extends State(false)
case object ReturnExpr extends State(true)
case object FailExpr extends State(true)
case object EvalRules extends State(false)
case object EvalMatch extends State(false)
case object ReturnMatch extends State(false)
case object FailMatch extends State(false)

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
    } while (!stack.isEmpty || !state.isTermination)
    if (state == FailExpr)
      UncaughtException
    else
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
    case Z      => state = ReturnExpr
    case S(e) => {
      expr = e
      stack = SStk :: stack
    }
    case Lam(x, t, e) => state = ReturnExpr
    case Let(n, d, b) => {
      expr = d
      stack = LetStk(n, b) :: stack
    }
    case Ap(e1, e2) => {
      expr = e1
      stack = ApStk(e2) :: stack
    }
    case Fix(x, t, e) => {
      expr = subst(Map(x -> Fix(x, t, e)))(e)
    }
    case Triv => state = ReturnExpr
    case Pairr(e1, e2) => {
      expr = e1
      stack = PairrStk(e2) :: stack
    }
    case ProjL(e) => {
      expr = e
      stack = ProjLStk :: stack
    }
    case ProjR(e) => {
      expr = e
      stack = ProjRStk :: stack
    }
    case Abort(t, e) => {
      expr = e
      stack = AbortStk :: stack
    }
    case InL(t, e) => {
      expr = e
      stack = InLStk :: stack
    }
    case InR(t, e) => {
      expr = e
      stack = InRStk :: stack
    }
    case Match(e, rs) => {
      expr = e
      stack = MatchStk(rs) :: stack
    }
    case Fold(x, t, e) => {
      expr = e
      stack = FoldStk(x) :: stack
    }
    case Unfold(e) => {
      expr = e
      stack = UnfoldStk :: stack
    }
    case TLam(x, e) => expr = e
    case TAp(e, t)  => expr = e
    case Raise(t)   => state = FailExpr
    case Catch(e1, e2) => {
      expr = e1
      stack = CatchStk(e2) :: stack
    }
    case UncaughtException => state = FailExpr
  }

  private def returnExpr : Unit = stack match {
    case Nil => ()
    case SStk :: ss => {
      expr = S(expr)
      stack = ss
    }
    case LetStk(n, b) :: ss => {
      expr = subst(Map(n -> expr))(b)
      stack = ss
      state = EvalExpr
    }
    case ApStk(e2 : Expr) :: ss => expr match {
      case Lam(x, t, b) => {
        expr = e2
        stack = Ap2Stk(x, b) :: ss
        state = EvalExpr
      }
      case _ => throw new Exception("application of non-function " + expr)
    }
    case Ap2Stk(x, b) :: ss => {
      expr = subst(Map(x -> expr))(b)
      stack = ss
      state = EvalExpr
    }
    case PairrStk(e2 : Expr) :: ss => {
      stack = Pairr2Stk(expr) :: ss
      expr = e2
      state = EvalExpr
    }
    case Pairr2Stk(e1 : Expr) :: ss => {
      expr = Pairr(e1, expr)
      stack = ss
    }
    case ProjLStk :: ss => expr match {
      case Pairr(e1, e2) => {
        expr = e1
        stack = ss
      }
      case _ => throw new Exception("projL of non-pair " + expr)
    }
    case ProjRStk :: ss => expr match {
      case Pairr(e1, e2) => {
        expr = e2
        stack = ss
      }
      case _ => throw new Exception("projR of non-pair " + expr)
    }
    case AbortStk :: ss => {
      expr = Abort(Unitt, expr)
      stack = ss
    }
    case InLStk :: ss => {
      expr = InL(Unitt, expr)
      stack = ss
    }
    case InRStk :: ss => {
      expr = InR(Unitt, expr)
      stack = ss
    }
    case MatchStk(rs) :: ss => {
      stack = ss
      rules = rs
      state = EvalRules
    }
    case FoldStk(x : String) :: ss => {
      expr = Fold(x, Unitt, expr)
      stack = ss
    }
    case UnfoldStk :: ss => expr match {
      case Fold(x, t, e) => {
        expr = e
        stack = ss
      }
      case _ => throw new Exception("unfold of non-fold " + expr)
    }
    case CatchStk(e2) :: ss          => stack = ss
    case PatStkRules(e, b, rs) :: ss => throw new Exception("pattern matching on stack during eval")
    case PairPatStk(p2, e2) :: ss    => throw new Exception("pattern matching on stack during eval")
    case Pair2PatStk(bind1) :: ss    => throw new Exception("pattern matching on stack during eval")
  }

  private def failExpr : Unit = stack match {
    case Nil                        => expr = UncaughtException
    case SStk :: ss                 => stack = ss
    case LetStk(n, b) :: ss         => stack = ss
    case ApStk(e2 : Expr) :: ss     => stack = ss
    case Ap2Stk(x, b) :: ss         => stack = ss
    case PairrStk(e2 : Expr) :: ss  => stack = ss
    case Pairr2Stk(e1 : Expr) :: ss => stack = ss
    case ProjLStk :: ss             => stack = ss
    case ProjRStk :: ss             => stack = ss
    case AbortStk :: ss             => stack = ss
    case InLStk :: ss               => stack = ss
    case InRStk :: ss               => stack = ss
    case MatchStk(rs) :: ss         => stack = ss
    case FoldStk(x : String) :: ss  => stack = ss
    case UnfoldStk :: ss            => stack = ss
    case CatchStk(e2) :: ss => {
      expr = e2
      stack = ss
      state = EvalExpr
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
      state = EvalMatch
    }
  }

  private def evalMatch : Unit = comp match {
    case (WildPat, _) => {
      bind = Map()
      state = ReturnMatch
    }
    case (VarPat(x), e) => {
      bind = Map(x -> e)
      state = ReturnMatch
    }
    case (TrivPat, Triv) => {
      bind = Map()
      state = ReturnMatch
    }
    case (PairPat(p1, p2), Pairr(e1, e2)) => {
      stack = PairPatStk(p2, e2) :: stack
      comp = (p1, e1)
    }
    case (InLPat(p), InL(t, e)) => comp = (p, e)
    case (InRPat(p), InR(t, e)) => comp = (p, e)
    case (ZPat, Z) => {
      bind = Map()
      state = ReturnMatch
    }
    case (SPat(p), S(e)) => comp = (p, e)
    case _               => state = FailMatch
  }

  private def returnMatch : Unit = stack match {
    case PatStkRules(e, b, rs) :: ss => {
      expr = subst(bind)(b)
      stack = ss
      state = EvalExpr
    }
    case PairPatStk(p2, e2) :: ss => {
      stack = Pair2PatStk(bind) :: ss
      comp = (p2, e2)
      state = EvalMatch
    }
    case Pair2PatStk(bind1) :: ss => {
      stack = ss
      bind = bind1 ++ bind
    }
    case _ => throw new Exception("no pattern rules on stack")
  }

  private def failMatch : Unit = stack match {
    case PatStkRules(e, b, rs) :: ss => {
      expr = e
      stack = ss
      rules = rs
      state = EvalRules
    }
    case PairPatStk(p2, e2) :: ss => stack = ss
    case Pair2PatStk(bind1) :: ss => stack = ss
    case _                        => throw new Exception("no pattern rules on stack")
  }

}