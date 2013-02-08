package compiler

import model.{ Z, Var, Triv, S, ProjR, ProjL, Pairr, Lam, Fix, Expr, Ap }
import model.InR
import model.Match
import model.InL
import model.Abort
import model.SPat
import model.TrivPat
import model.InRPat
import model.PairPat
import model.InLPat
import model.VarPat
import model.WildPat
import model.ZPat
import model.Pattern
import interpreter.Substitutor.subst
import model.Unfold
import model.Fold
import model.Let
import model.TLam
import model.TAp
import model.Unitt
import model.Raise
import model.UncaughtException
import model.Catch

object Compiler {

  def eval(e : Expr) : Expr = evalExpr(e)(Nil)

  private def evalExpr(e : Expr)(ss : List[Stack]) : Expr = e match {
    case Var(x)            => throw new Exception("unsubstituted variable " + x)
    case Z                 => returnExpr(Z)(ss)
    case S(e)              => evalExpr(e)(SStk :: ss)
    case Lam(x, t, e)      => returnExpr(Lam(x, t, e))(ss)
    case Let(n, d, b)      => evalExpr(d)(LetStk(n, b) :: ss)
    case Ap(e1, e2)        => evalExpr(e1)(ApStk(e2) :: ss)
    case Fix(x, t, e)      => evalExpr(subst(Map(x -> Fix(x, t, e)))(e))(ss)
    case Triv              => returnExpr(Triv)(ss)
    case Pairr(e1, e2)     => evalExpr(e1)(PairrStk(e2) :: ss)
    case ProjL(e)          => evalExpr(e)(ProjLStk :: ss)
    case ProjR(e)          => evalExpr(e)(ProjRStk :: ss)
    case Abort(t, e)       => evalExpr(e)(AbortStk :: ss)
    case InL(t, e)         => evalExpr(e)(InLStk :: ss)
    case InR(t, e)         => evalExpr(e)(InRStk :: ss)
    case Match(e, rs)      => evalExpr(e)(MatchStk(rs) :: ss)
    case Fold(x, t, e)     => evalExpr(e)(FoldStk(x) :: ss)
    case Unfold(e)         => evalExpr(e)(UnfoldStk :: ss)
    case TLam(x, e)        => evalExpr(e)(ss) //ignore types at runtime
    case TAp(e, t)         => evalExpr(e)(ss) //ignore types at runtime
    case Raise(t)          => failExpr(ss)
    case Catch(e1, e2)     => evalExpr(e1)(CatchStk(e2) :: ss)
    case UncaughtException => failExpr(ss)
  }

  private def returnExpr(e : Expr)(ss : List[Stack]) : Expr = ss match {
    case Nil                => e
    case SStk :: ss         => returnExpr(S(e))(ss)
    case LetStk(n, b) :: ss => evalExpr(subst(Map(n -> e))(b))(ss)
    case ApStk(e2 : Expr) :: ss => e match {
      case Lam(x, t, b) => evalExpr(e2)(Ap2Stk(x, b) :: ss)
      case _            => throw new Exception("application of non-function " + e)
    }
    case Ap2Stk(x, b) :: ss         => evalExpr(subst(Map(x -> e))(b))(ss)
    case PairrStk(e2 : Expr) :: ss  => evalExpr(e2)(Pairr2Stk(e) :: ss)
    case Pairr2Stk(e1 : Expr) :: ss => returnExpr(Pairr(e1, e))(ss)
    case ProjLStk :: ss => e match {
      case Pairr(e1, e2) => returnExpr(e1)(ss)
      case _             => throw new Exception("projL of non-pair " + e)
    }
    case ProjRStk :: ss => e match {
      case Pairr(e1, e2) => returnExpr(e2)(ss)
      case _             => throw new Exception("projR of non-pair " + e)
    }
    case AbortStk :: ss            => returnExpr(Abort(Unitt, e))(ss)
    case InLStk :: ss              => returnExpr(InL(Unitt, e))(ss)
    case InRStk :: ss              => returnExpr(InR(Unitt, e))(ss)
    case MatchStk(rs) :: ss        => evalRules(e)(rs)(ss)
    case FoldStk(x : String) :: ss => returnExpr(Fold(x, Unitt, e))(ss)
    case UnfoldStk :: ss => e match {
      case Fold(x, t, e) => returnExpr(e)(ss)
      case _             => throw new Exception("unfold of non-fold " + e)
    }
    case CatchStk(e2) :: ss => returnExpr(e)(ss)
  }

  private def failExpr(ss : List[Stack]) : Expr = ss match {
    case Nil                => UncaughtException
    case CatchStk(e2) :: ss => evalExpr(e2)(ss)
    case _ :: ss            => failExpr(ss)
  }

  private def evalRules(e : Expr)(ss : List[(Pattern, Expr)])(out : List[Stack]) : Expr = ss match {
    case Nil          => throw new Exception("no match found for " + e)
    case (p, b) :: rs => evalMatch(p, e)(Nil)(RulesStack(e, b, rs))(out)
  }

  private def evalMatch(p : Pattern, e : Expr)(ss : List[PatStack])(rs : RulesStack)(out : List[Stack]) : Expr = (p, e) match {
    case (WildPat, _)                     => returnMatch(Map())(ss)(rs)(out)
    case (VarPat(x), e)                   => returnMatch(Map(x -> e))(ss)(rs)(out)
    case (TrivPat, Triv)                  => returnMatch(Map())(ss)(rs)(out)
    case (PairPat(p1, p2), Pairr(e1, e2)) => evalMatch(p1, e1)(PairPatStk(p2, e2) :: ss)(rs)(out)
    case (InLPat(p), InL(t, e))           => evalMatch(p, e)(ss)(rs)(out)
    case (InRPat(p), InR(t, e))           => evalMatch(p, e)(ss)(rs)(out)
    case (ZPat, Z)                        => returnMatch(Map())(ss)(rs)(out)
    case (SPat(p), S(e))                  => evalMatch(p, e)(ss)(rs)(out)
    case _                                => failMatch(ss)(rs)(out)
  }

  private def returnMatch(bind : Map[String, Expr])(ss : List[PatStack])(rs : RulesStack)(out : List[Stack]) : Expr = ss match {
    case Nil                      => evalExpr(subst(bind)(rs.b))(out)
    case PairPatStk(p2, e2) :: ss => evalMatch(p2, e2)(Pair2PatStk(bind) :: ss)(rs)(out)
    case Pair2PatStk(bind1) :: ss => returnMatch(bind1 ++ bind)(ss)(rs)(out)
  }

  //just pops stack; for if we ever need to fold the stacks together
  private def failMatch(ss : List[PatStack])(rs : RulesStack)(out : List[Stack]) : Expr = ss match {
    case Nil                      => evalRules(rs.e)(rs.rs)(out)
    case PairPatStk(p2, e2) :: ss => failMatch(ss)(rs)(out)
    case Pair2PatStk(bind1) :: ss => failMatch(ss)(rs)(out)
  }

}