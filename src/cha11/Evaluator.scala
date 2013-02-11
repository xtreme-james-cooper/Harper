package cha11

object Evaluator {

  def evalExpr : Expr => Value = {
    case Var(x)         => throw new Exception("unbound variable " + x)
    case Z              => ZVal
    case S(e)           => SVal(evalExpr(e))
    case Let(e1, x, e2) => evalExpr(subst(Map(x -> evalExpr(e1).toExpr))(e2))
    case Lam(t, x, e)   => LamVal(t, x, e)
    case Ap(e1, e2) => {
      val lam = evalExpr(e1).asInstanceOf[LamVal]
      evalExpr(subst(Map(lam.x -> evalExpr(e2).toExpr))(lam.e))
    }
    case IfZ(e, e0, x, e1) => evalExpr(e) match {
      case ZVal    => evalExpr(e0)
      case SVal(n) => evalExpr(subst(Map(x -> n.toExpr))(e1))
      case _       => throw new ClassCastException
    }
    case Fix(t, x, e) => evalExpr(subst(Map(x -> Fix(t, x, e)))(e))
    case Pair(e1, e2) => PairVal(evalExpr(e1), evalExpr(e2))
    case PrR(e)       => evalExpr(e).asInstanceOf[PairVal].v2
    case PrL(e)       => evalExpr(e).asInstanceOf[PairVal].v1
    case Triv         => TrivVal
  }

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
    case IfZ(e, e0, x0, e1) => {
      val nv = newVar
      IfZ(subst(m)(e), subst(m)(e0), nv, subst(m)(subst(Map(x0 -> Var(nv)))(e1)))
    }
    case Fix(t, x, e) => {
      val nv = newVar
      Fix(t, nv, subst(m)(subst(Map(x -> Var(nv)))(e)))
    }
    case Pair(e1, e2) => Pair(subst(m)(e1), subst(m)(e2))
    case PrR(e)       => PrR(subst(m)(e))
    case PrL(e)       => PrL(subst(m)(e))
    case Triv         => Triv
  }

}