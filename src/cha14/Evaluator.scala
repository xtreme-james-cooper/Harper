package cha14

object Evaluator {

  def evalExpr : Expr => Value = {
    case Var(x)         => throw new Exception("unbound variable " + x)
    case Z              => ZVal
    case S(e)           => SVal(evalExpr(e))
    case Let(e1, x, e2) => evalExpr(subst(Map(x -> evalExpr(e1).toExpr))(e2))
    case Lam(t, x, e)   => LamVal(x, e)
    case Ap(e1, e2) => {
      val lam = evalExpr(e1).asInstanceOf[LamVal]
      evalExpr(subst(Map(lam.x -> evalExpr(e2).toExpr))(lam.e))
    }
    case Fix(t, x, e) => evalExpr(subst(Map(x -> Fix(t, x, e)))(e))
    case Pair(e1, e2) => PairVal(evalExpr(e1), evalExpr(e2))
    case PrR(e)       => evalExpr(e).asInstanceOf[PairVal].v2
    case PrL(e)       => evalExpr(e).asInstanceOf[PairVal].v1
    case Triv         => TrivVal
    case Abort(t, e)  => evalExpr(e) //Not quite correct, but ok because abort is non-terminating
    case InL(t, e)    => InLVal(evalExpr(e))
    case InR(t, e)    => InRVal(evalExpr(e))
    case Match(e, rs) => evalRules(evalExpr(e))(rs)
    case Generic(tx, t, x, xt, e0, e) => evalExpr(t match {
      case VarTy(y)       => if (tx == y) subst(Map(x -> e))(e0) else e
      case NumTy          => e
      case ArrTy(t1, t2)  => throw new Exception("cannot use map over arrow type")
      case ProdTy(t1, t2) => Pair(Generic(tx, t1, x, xt, e0, PrL(e)), Generic(tx, t2, x, xt, e0, PrR(e)))
      case UnitTy         => e
      case VoidTy         => e
      case SumTy(t1, t2) => {
        val nv1 = newVar
        val nv2 = newVar
        Match(e, List(
          (InLPat(VarPat(nv1)), InL(SumTy(t1, t2), Generic(tx, t1, x, xt, e0, Var(nv1)))),
          (InRPat(VarPat(nv2)), InR(SumTy(t1, t2), Generic(tx, t2, x, xt, e0, Var(nv2))))))
      }
    })
  }

  private def evalRules(e : Value) : List[(Pattern, Expr)] => Value = {
    case Nil => throw new Exception("no match for case " + e)
    case (p, b) :: rs => doMatch(p, e) match {
      case None       => evalRules(e)(rs)
      case Some(bind) => evalExpr(subst(bind)(b))
    }
  }

  private def doMatch : (Pattern, Value) => Option[Map[String, Expr]] = {
    case (WildPat, _)       => Some(Map())
    case (VarPat(x), e)     => Some(Map(x -> e.toExpr))
    case (TrivPat, TrivVal) => Some(Map())
    case (PairPat(p1, p2), PairVal(e1, e2)) =>
      for {
        b1 <- doMatch(p1, e1)
        b2 <- doMatch(p2, e2)
      } yield b1 ++ b2
    case (InLPat(p), InLVal(e)) => doMatch(p, e)
    case (InRPat(p), InRVal(e)) => doMatch(p, e)
    case (ZPat, ZVal)           => Some(Map())
    case (SPat(p), SVal(e))     => doMatch(p, e)
    case _                      => None
  }

  /*--------------------------*/

  private var varTag : Int = 0

  private def newVar : String = {
    varTag = varTag + 1
    "var-" + varTag
  }

  private def subst(m : Map[String, Expr]) : Expr => Expr = {
    case Var(y) => if (m.contains(y)) m(y) else Var(y)
    case Z      => Z
    case S(e)   => S(subst(m)(e))
    case Let(e1, y, e2) => {
      val nv = newVar
      Let(subst(m)(e1), nv, subst(m)(subst(Map(y -> Var(nv)))(e2)))
    }
    case Lam(t, y, e) => {
      val nv = newVar
      Lam(t, nv, subst(m)(subst(Map(y -> Var(nv)))(e)))
    }
    case Ap(e1, e2) => Ap(subst(m)(e1), subst(m)(e2))
    case Fix(t, x, e) => {
      val nv = newVar
      Fix(t, nv, subst(m)(subst(Map(x -> Var(nv)))(e)))
    }
    case Pair(e1, e2) => Pair(subst(m)(e1), subst(m)(e2))
    case PrR(e)       => PrR(subst(m)(e))
    case PrL(e)       => PrL(subst(m)(e))
    case Triv         => Triv
    case Abort(t, e)  => Abort(t, subst(m)(e))
    case InL(t, e)    => InL(t, subst(m)(e))
    case InR(t, e)    => InR(t, subst(m)(e))
    case Match(e, rs) => Match(subst(m)(e), rs.map({ case (p, e) => substRule(m)(p, e) }))
    case Generic(tx, t, x, xt, e0, e) => {
      val nv = newVar
      Generic(tx, t, nv, xt, subst(m)(subst(Map(x -> Var(nv)))(e0)), subst(m)(e))
    }
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

}