package cha09

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
    case Rec(e0, x, y, e1, e) => evalExpr(e) match {
      case ZVal => evalExpr(e0)
      case SVal(n) => evalExpr(subst(Map(x -> n.toExpr, y -> Rec(e0, x, y, e1, n.toExpr)))(e1))
      case LamVal(_, _, _) => throw new ClassCastException
    }
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
    case Rec(e0, x0, y0, e1, e) => {
      val xnv = newVar
      val ynv = newVar
      Rec(subst(m)(e0), xnv, ynv, subst(m)(subst(Map(x0 -> Var(xnv), y0 -> Var(ynv)))(e1)), subst(m)(e))
    }
  }

}