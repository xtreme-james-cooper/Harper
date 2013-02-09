package all.interpreter

import all.model.{ Z, Var, Triv, S, ProjR, ProjL, Pairr, Lam, Fix, Expr, Ap }
import all.model.Abort
import all.model.InR
import all.model.InL
import all.model.Match
import all.model.Pattern
import all.model.SPat
import all.model.TrivPat
import all.model.InRPat
import all.model.PairPat
import all.model.InLPat
import all.model.VarPat
import all.model.WildPat
import all.model.ZPat
import all.model.Type
import all.model.Nat
import all.model.TyVar
import all.model.Unitt
import all.model.Arr
import all.model.Rec
import all.model.Voidd
import all.model.Prod
import all.model.Sum
import all.model.Unfold
import all.model.Fold
import all.model.Let
import all.model.All
import all.model.TLam
import all.model.TAp
import all.model.Raise
import all.model.Catch
import all.model.UncaughtException

object Substitutor {

  private var varTag : Int = 0

  private def newVar : String = {
    varTag = varTag + 1
    "var-" + varTag
  }

  def subst(bind : Map[String, Expr]) : Expr => Expr = {
    case Var(y) => bind.getOrElse(y, Var(y))
    case Z      => Z
    case S(n)   => S(subst(bind)(n))
    case Lam(y, t, e) => {
      val newV : String = newVar
      Lam(newV, t, subst(bind + (y -> Var(newV)))(e))
    }
    case Let(n, d, b) => {
      val newV : String = newVar
      Let(newV, subst(bind)(d), subst(bind + (n -> Var(newV)))(b))
    }
    case Ap(e1, e2) => Ap(subst(bind)(e1), subst(bind)(e2))
    case Fix(y, t, e) => {
      val newV : String = newVar
      Fix(newV, t, subst(bind + (y -> Var(newV)))(e))
    }
    case Triv              => Triv
    case Pairr(e1, e2)     => Pairr(subst(bind)(e1), subst(bind)(e2))
    case ProjL(e)          => ProjL(subst(bind)(e))
    case ProjR(e)          => ProjR(subst(bind)(e))
    case Abort(t, e)       => Abort(t, subst(bind)(e))
    case InL(t, e)         => InL(t, subst(bind)(e))
    case InR(t, e)         => InR(t, subst(bind)(e))
    case Match(e, rs)      => Match(subst(bind)(e), rs.map({ case (p, e) => substRule(bind)(p, e) }))
    case Fold(x, t, e)     => Fold(x, t, subst(bind)(e))
    case Unfold(e)         => Unfold(subst(bind)(e))
    case TLam(y, e)        => TLam(y, subst(bind)(e))
    case TAp(e, t)         => TAp(subst(bind)(e), t)
    case Raise(t)          => Raise(t)
    case Catch(e1, e2)     => Catch(subst(bind)(e1), subst(bind)(e2))
    case UncaughtException => UncaughtException
  }

  private def substRule(bind : Map[String, Expr]) : (Pattern, Expr) => (Pattern, Expr) = (p, e) => {
    val patternBinds : Map[String, String] = Map() ++ (for (x <- p.freeVars) yield (x, newVar))
    (substPat(patternBinds)(p), subst(bind ++ patternBinds.map({ case (x, v) => (x, Var(v)) }))(e))
  }

  private def substPat(bind : Map[String, String]) : Pattern => Pattern = {
    case WildPat         => WildPat
    case VarPat(x)       => VarPat(bind.getOrElse(x, x))
    case TrivPat         => TrivPat
    case PairPat(p1, p2) => PairPat(substPat(bind)(p1), substPat(bind)(p2))
    case InLPat(p)       => InLPat(substPat(bind)(p))
    case InRPat(p)       => InRPat(substPat(bind)(p))
    case ZPat            => ZPat
    case SPat(p)         => SPat(substPat(bind)(p))
  }

  def substT(x : String, t : Type) : Type => Type = {
    case Nat          => Nat
    case Arr(t1, t2)  => Arr(substT(x, t)(t1), substT(x, t)(t2))
    case Unitt        => Unitt
    case Prod(t1, t2) => Prod(substT(x, t)(t1), substT(x, t)(t2))
    case Voidd        => Voidd
    case Sum(t1, t2)  => Sum(substT(x, t)(t1), substT(x, t)(t2))
    case TyVar(y) =>
      if (x == y) t
      else TyVar(y)
    case Rec(y, t1) => {
      val newV : String = newVar
      Rec(newV, substT(x, t)(substT(y, TyVar(newV))(t1)))
    }
    case All(y, t1) => {
      val newV : String = newVar
      All(newV, substT(x, t)(substT(y, TyVar(newV))(t1)))
    }
  }

}