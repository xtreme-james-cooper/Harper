package compiler

import model.{ ZPat, Z, WildPat, VarPat, Var, Unitt, Unfold, UncaughtException, TrivPat, Triv, TLam, TAp, SPat, S, Raise, ProjR, ProjL, Pattern, Pairr, PairPat, Match, Let, Lam, InRPat, InR, InLPat, InL, Fold, Fix, Expr, Catch, Ap, Abort }
import interpreter.Substitutor.subst

object StateMachine {

  private var state : State = null
  private var expr : Expr = null
  private var stack : List[Stack] = null
  private var rules : List[(Pattern, Expr)] = null
  private var pattern : Pattern = null
  private var bind : Map[String, Expr] = null

  def eval(e : Expr) : Expr = {
    state = EvalExpr
    expr = e
    stack = Nil

    while (!(stack.isEmpty && state.isTermination)) {
      doStep
    }

    if (state == Throw)
      UncaughtException
    else
      expr
  }

  private def doStep : Unit = state match {
    case EvalExpr  => evalExpr
    case Return    => returnn
    case Throw     => throwExpr
    case EvalRules => evalRules
    case EvalMatch => evalMatch
  }

  private def pop : Stack = {
    val hed = stack.head
    stack = stack.tail
    hed
  }

  private def push(s : Stack) : Unit = stack = s :: stack

  private def evalExpr : Unit = expr match {
    case Var(x) => throw new Exception("unsubstituted variable " + x)
    case Z      => state = Return
    case S(e) => {
      expr = e
      push(SStk)
    }
    case Lam(x, t, e) => state = Return
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
    case Triv => state = Return
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
    case Raise(t)   => state = Throw
    case Catch(e1, e2) => {
      expr = e1
      push(CatchStk(e2))
    }
    case UncaughtException => state = Throw
  }

  //Covers both value return and successful pattern match return
  private def returnn : Unit = pop match {
    case SStk => expr = S(expr)
    case LetStk(n, b) => {
      expr = subst(Map(n -> expr))(b)
      state = EvalExpr
    }
    case ApStk(e2) => {
      push(Ap2Stk(expr.asInstanceOf[Lam].x, expr.asInstanceOf[Lam].e))
      expr = e2
      state = EvalExpr
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
    case ProjLStk      => expr = expr.asInstanceOf[Pairr].e1
    case ProjRStk      => expr = expr.asInstanceOf[Pairr].e2
    case AbortStk      => expr = Abort(Unitt, expr)
    case InLStk        => expr = InL(Unitt, expr)
    case InRStk        => expr = InR(Unitt, expr)
    case MatchStk(rs) => {
      rules = rs
      state = EvalRules
    }
    case FoldStk(x)   => expr = Fold(x, Unitt, expr)
    case UnfoldStk    => expr = expr.asInstanceOf[Fold].e
    case CatchStk(e2) => ()
    case PatStkRules(e, b, rs) => {
      expr = subst(bind)(b)
      state = EvalExpr
    }
    case PairPatStk(p2, e2) => {
      push(Pair2PatStk(bind))
      pattern = p2
      expr = e2
      state = EvalMatch
    }
    case Pair2PatStk(bind1) => bind = bind1 ++ bind
  }

  //Covers both exception throwing and pattern-match-failure
  private def throwExpr : Unit = pop match {
    case CatchStk(e2) => {
      expr = e2
      state = EvalExpr
    }
    case PatStkRules(e, b, rs) => {
      expr = e
      rules = rs
      state = EvalRules
    }
    case _ => ()
  }

  private def evalRules : Unit = rules match {
    case Nil => state = Throw
    case (p, b) :: rs => {
      push(PatStkRules(expr, b, rs))
      pattern = p
      state = EvalMatch
    }
  }

  private def evalMatch : Unit = (pattern, expr) match {
    case (WildPat, _) => {
      bind = Map()
      state = Return
    }
    case (VarPat(x), e) => {
      bind = Map(x -> e)
      state = Return
    }
    case (TrivPat, Triv) => {
      bind = Map()
      state = Return
    }
    case (PairPat(p1, p2), Pairr(e1, e2)) => {
      push(PairPatStk(p2, e2))
      pattern = p1
      expr = e1
    }
    case (InLPat(p), InL(t, e)) => {
      pattern = p
      expr = e
    }
    case (InRPat(p), InR(t, e)) => {
      pattern = p
      expr = e
    }
    case (ZPat, Z) => {
      bind = Map()
      state = Return
    }
    case (SPat(p), S(e)) => {
      pattern = p
      expr = e
    }
    case _ => state = Throw
  }


}