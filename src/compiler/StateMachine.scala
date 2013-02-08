package compiler

import model.{ ZPat, Z, WildPat, VarPat, Var, Unitt, Unfold, UncaughtException, TrivPat, Triv, TLam, TAp, SPat, S, Raise, ProjR, ProjL, Pattern, Pairr, PairPat, Match, Let, Lam, InRPat, InR, InLPat, InL, Fold, Fix, Expr, Catch, Ap, Abort }
import interpreter.Substitutor.subst

sealed abstract class State(val isTermination : Boolean)
case object EvalExpr extends State(false)
case object ReturnExpr extends State(true)
case object ThrowExpr extends State(true)
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

    if (state == ThrowExpr)
      UncaughtException
    else
      expr
  }

  private def doStep : Unit = state match {
    case EvalExpr    => evalExpr
    case ReturnExpr  => returnExpr
    case ThrowExpr   => throwExpr
    case EvalRules   => evalRules
    case EvalMatch   => evalMatch
    case ReturnMatch => returnMatch
    case FailMatch   => failMatch
  }

  private def pop : Stack = {
    val hed = stack.head
    stack = stack.tail
    hed
  }
  
  private def push(s : Stack) : Unit = stack = s :: stack

  private def evalExpr : Unit = expr match {
    case Var(x) => throw new Exception("unsubstituted variable " + x)
    case Z      => state = ReturnExpr
    case S(e) => {
      expr = e
      push(SStk)
    }
    case Lam(x, t, e) => state = ReturnExpr
    case Let(n, d, b) => {
      expr = d
      push(LetStk(n, b))
    }
    case Ap(e1, e2) => {
      expr = e1
      push(ApStk(e2))
    }
    case Fix(x, t, e) => {
      expr = subst(Map(x -> Fix(x, t, e)))(e)
    }
    case Triv => state = ReturnExpr
    case Pairr(e1, e2) => {
      expr = e1
      push(PairrStk(e2))
    }
    case ProjL(e) => {
      expr = e
      push(ProjLStk)
    }
    case ProjR(e) => {
      expr = e
      push(ProjRStk)
    }
    case Abort(t, e) => {
      expr = e
      push(AbortStk)
    }
    case InL(t, e) => {
      expr = e
      push(InLStk)
    }
    case InR(t, e) => {
      expr = e
      push(InRStk)
    }
    case Match(e, rs) => {
      expr = e
      push(MatchStk(rs))
    }
    case Fold(x, t, e) => {
      expr = e
      push(FoldStk(x))
    }
    case Unfold(e) => {
      expr = e
      push(UnfoldStk)
    }
    case TLam(x, e) => expr = e
    case TAp(e, t)  => expr = e
    case Raise(t)   => state = ThrowExpr
    case Catch(e1, e2) => {
      expr = e1
      push(CatchStk(e2))
    }
    case UncaughtException => state = ThrowExpr
  }

  private def returnExpr : Unit = pop match {
    case SStk => expr = S(expr)
    case LetStk(n, b) => {
      expr = subst(Map(n -> expr))(b)
      state = EvalExpr
    }
    case ApStk(e2) => expr match {
      case Lam(x, t, b) => {
        expr = e2
        push(Ap2Stk(x, b))
        state = EvalExpr
      }
      case _ => throw new Exception("application of non-function " + expr)
    }
    case Ap2Stk(x, b) => {
      expr = subst(Map(x -> expr))(b)
      state = EvalExpr
    }
    case PairrStk(e2) => {
      push(Pairr2Stk(expr))
      expr = e2
      state = EvalExpr
    }
    case Pairr2Stk(e1) => expr = Pairr(e1, expr)
    case ProjLStk => expr match {
      case Pairr(e1, e2) => expr = e1
      case _             => throw new Exception("projL of non-pair " + expr)
    }
    case ProjRStk => expr match {
      case Pairr(e1, e2) => expr = e2
      case _             => throw new Exception("projR of non-pair " + expr)
    }
    case AbortStk => expr = Abort(Unitt, expr)
    case InLStk   => expr = InL(Unitt, expr)
    case InRStk   => expr = InR(Unitt, expr)
    case MatchStk(rs) => {
      rules = rs
      state = EvalRules
    }
    case FoldStk(x) => expr = Fold(x, Unitt, expr)
    case UnfoldStk => expr match {
      case Fold(x, t, e) => expr = e
      case _             => throw new Exception("unfold of non-fold " + expr)
    }
    case CatchStk(e2)          => ()
    case PatStkRules(e, b, rs) => throw new Exception("pattern matching on stack during eval")
    case PairPatStk(p2, e2)    => throw new Exception("pattern matching on stack during eval")
    case Pair2PatStk(bind1)    => throw new Exception("pattern matching on stack during eval")
  }

  private def throwExpr : Unit = pop match {
    case CatchStk(e2) => {
      expr = e2
      state = EvalExpr
    }
    case PatStkRules(e, b, rs) => throw new Exception("pattern matching on stack during eval")
    case PairPatStk(p2, e2)    => throw new Exception("pattern matching on stack during eval")
    case Pair2PatStk(bind1)    => throw new Exception("pattern matching on stack during eval")
    case _                     => ()
  }

  private def evalRules : Unit = rules match {
    case Nil => throw new Exception("no match found for " + expr)
    case (p, b) :: rs => {
      push(PatStkRules(expr, b, rs))
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
      push(PairPatStk(p2, e2))
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

  private def returnMatch : Unit = pop match {
    case PatStkRules(e, b, rs) => {
      expr = subst(bind)(b)
      state = EvalExpr
    }
    case PairPatStk(p2, e2) => {
      push(Pair2PatStk(bind))
      comp = (p2, e2)
      state = EvalMatch
    }
    case Pair2PatStk(bind1) => bind = bind1 ++ bind
    case _                  => throw new Exception("no pattern rules on stack")
  }

  private def failMatch : Unit = pop match {
    case PatStkRules(e, b, rs) => {
      expr = e
      rules = rs
      state = EvalRules
    }
    case PairPatStk(p2, e2) => ()
    case Pair2PatStk(bind1) => ()
    case _                  => throw new Exception("no pattern rules on stack")
  }

}