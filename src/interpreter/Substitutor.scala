package interpreter

import model.{ Z, Var, Triv, S, ProjR, ProjL, Pairr, Lam, Fix, Expr, Ap }
import model.Abort
import model.InR
import model.InL
import model.Match
import model.Pattern
import model.SPat
import model.TrivPat
import model.InRPat
import model.PairPat
import model.InLPat
import model.VarPat
import model.WildPat
import model.ZPat

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
    case Ap(e1, e2) => Ap(subst(bind)(e1), subst(bind)(e2))
    case Fix(y, t, e) => {
      val newV : String = newVar
      Fix(newV, t, subst(bind + (y -> Var(newV)))(e))
    }
    case Triv          => Triv
    case Pairr(e1, e2) => Pairr(subst(bind)(e1), subst(bind)(e2))
    case ProjL(e)      => ProjL(subst(bind)(e))
    case ProjR(e)      => ProjR(subst(bind)(e))
    case Abort(t, e)   => Abort(t, subst(bind)(e))
    case InL(t, e)     => InL(t, subst(bind)(e))
    case InR(t, e)     => InR(t, subst(bind)(e))
    case Match(e, rs)  => Match(subst(bind)(e), rs.map({ case (p, e) => substRule(bind)(p, e) }))
  }

  private def substRule(bind : Map[String, Expr]) : (Pattern, Expr) => (Pattern, Expr) = (p, e) => {
    val patternBinds = Map() ++ (for (x <- p.freeVars) yield (x, newVar))
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

}