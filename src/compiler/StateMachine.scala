package compiler

import model.{ ZPat, Z, WildPat, VarPat, Var, Unitt, Unfold, UncaughtException, TrivPat, Triv, TLam, TAp, SPat, S, Raise, ProjR, ProjL, Pattern, Pairr, PairPat, Match, Let, Lam, InRPat, InR, InLPat, InL, Fold, Fix, Expr, Catch, Ap, Abort }
import interpreter.Substitutor.subst

object StateMachine {

  private var expr : Expr = null
  private var stack : List[Stack] = null

  def eval(e : Expr) : Expr = {
    expr = e
    stack = Nil
    evalExpr
  }

  private def evalExpr : Expr = expr match {
    case Var(x) => throw new Exception("unsubstituted variable " + x)
    case Z      => returnExpr(Z)
    case S(e) => {
      expr = e
      stack = SStk :: stack
      evalExpr
    }
    case Lam(x, t, e) => returnExpr(Lam(x, t, e))
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
    case Triv => returnExpr(Triv)
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
    case Raise(t) => failExpr(stack)
    case Catch(e1, e2) => {
      expr = e1
      stack = CatchStk(e2) :: stack
      evalExpr
    }
    case UncaughtException => failExpr(stack)
  }

  private def returnExpr(e : Expr) : Expr = stack match {
    case Nil => e
    case SStk :: ss => {
      stack = ss
      returnExpr(S(e))
    }
    case LetStk(n, b) :: ss => {
      expr = subst(Map(n -> e))(b)
      stack = ss
      evalExpr
    }
    case ApStk(e2 : Expr) :: ss => e match {
      case Lam(x, t, b) => {
        expr = e2
        stack = Ap2Stk(x, b) :: ss
        evalExpr
      }
      case _ => throw new Exception("application of non-function " + e)
    }
    case Ap2Stk(x, b) :: ss => {
      expr = subst(Map(x -> e))(b)
      stack = ss
      evalExpr
    }
    case PairrStk(e2 : Expr) :: ss => {
      expr = e2
      stack = Pairr2Stk(e) :: ss
      evalExpr
    }
    case Pairr2Stk(e1 : Expr) :: ss => {
      stack = ss
      returnExpr(Pairr(e1, e))
    }
    case ProjLStk :: ss => e match {
      case Pairr(e1, e2) => {
        stack = ss
        returnExpr(e1)
      }
      case _ => throw new Exception("projL of non-pair " + e)
    }
    case ProjRStk :: ss => e match {
      case Pairr(e1, e2) => {
        stack = ss
        returnExpr(e2)
      }
      case _ => throw new Exception("projR of non-pair " + e)
    }
    case AbortStk :: ss => {
      stack = ss
      returnExpr(Abort(Unitt, e))
    }
    case InLStk :: ss => {
      stack = ss
      returnExpr(InL(Unitt, e))
    }
    case InRStk :: ss => {
      stack = ss
      returnExpr(InR(Unitt, e))
    }
    case MatchStk(rs) :: ss => {
      stack = ss
      evalRules(e)(rs)
    }
    case FoldStk(x : String) :: ss => {
      stack = ss
      returnExpr(Fold(x, Unitt, e))
    }
    case UnfoldStk :: ss => e match {
      case Fold(x, t, e) => {
        stack = ss
        returnExpr(e)
      }
      case _ => throw new Exception("unfold of non-fold " + e)
    }
    case CatchStk(e2) :: ss => {
      stack = ss
      returnExpr(e)
    }
    case PatStkRules(e, b, rs) :: ss => throw new Exception("pattern matching on stack during eval")
    case PairPatStk(p2, e2) :: ss    => throw new Exception("pattern matching on stack during eval")
    case Pair2PatStk(bind1) :: ss    => throw new Exception("pattern matching on stack during eval")
  }

  private def failExpr(ss : List[Stack]) : Expr = ss match {
    case Nil                        => UncaughtException
    case SStk :: ss                 => failExpr(ss)
    case LetStk(n, b) :: ss         => failExpr(ss)
    case ApStk(e2 : Expr) :: ss     => failExpr(ss)
    case Ap2Stk(x, b) :: ss         => failExpr(ss)
    case PairrStk(e2 : Expr) :: ss  => failExpr(ss)
    case Pairr2Stk(e1 : Expr) :: ss => failExpr(ss)
    case ProjLStk :: ss             => failExpr(ss)
    case ProjRStk :: ss             => failExpr(ss)
    case AbortStk :: ss             => failExpr(ss)
    case InLStk :: ss               => failExpr(ss)
    case InRStk :: ss               => failExpr(ss)
    case MatchStk(rs) :: ss         => failExpr(ss)
    case FoldStk(x : String) :: ss  => failExpr(ss)
    case UnfoldStk :: ss            => failExpr(ss)
    case CatchStk(e2) :: ss => {
      expr = e2
      stack = ss
      evalExpr
    }
    case PatStkRules(e, b, rs) :: ss => throw new Exception("pattern matching on stack during eval")
    case PairPatStk(p2, e2) :: ss    => throw new Exception("pattern matching on stack during eval")
    case Pair2PatStk(bind1) :: ss    => throw new Exception("pattern matching on stack during eval")
  }

  private def evalRules(e : Expr)(ss : List[(Pattern, Expr)]) : Expr = ss match {
    case Nil          => throw new Exception("no match found for " + e)
    case (p, b) :: rs => {
      stack = PatStkRules(e, b, rs) :: stack
      evalMatch(p, e)
    }
  }

  private def evalMatch(p : Pattern, e : Expr) : Expr = (p, e) match {
    case (WildPat, _)                     => returnMatch(Map())
    case (VarPat(x), e)                   => returnMatch(Map(x -> e))
    case (TrivPat, Triv)                  => returnMatch(Map())
    case (PairPat(p1, p2), Pairr(e1, e2)) => {
      stack = PairPatStk(p2, e2) :: stack
      evalMatch(p1, e1)
    }
    case (InLPat(p), InL(t, e))           => evalMatch(p, e)
    case (InRPat(p), InR(t, e))           => evalMatch(p, e)
    case (ZPat, Z)                        => returnMatch(Map())
    case (SPat(p), S(e))                  => evalMatch(p, e)
    case _                                => failMatch
  }

  private def returnMatch(bind : Map[String, Expr]) : Expr = stack match {
    case PatStkRules(e, b, rs) :: ss => {
      expr = subst(bind)(b)
      stack = ss
      evalExpr
    }
    case PairPatStk(p2, e2) :: ss => {
      stack = Pair2PatStk(bind) :: ss
      evalMatch(p2, e2)
    }
    case Pair2PatStk(bind1) :: ss => {
      stack = ss
      returnMatch(bind1 ++ bind)
    }
    case _                        => throw new Exception("no pattern rules on stack")
  }

  private def failMatch : Expr = stack match {
    case PatStkRules(e, b, rs) :: ss => {
      stack = ss
      evalRules(e)(rs)
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