package cha08

object Evaluator {

  def evalExpr : Expr => Value = {
    case Var(x)         => throw new Exception("unbound variable " + x)
    case Str(s)         => StrVal(s)
    case Num(n)         => NumVal(n)
    case Plus(e1, e2)   => NumVal(evalExpr(e1).asInstanceOf[NumVal].n + evalExpr(e2).asInstanceOf[NumVal].n)
    case Times(e1, e2)  => NumVal(evalExpr(e1).asInstanceOf[NumVal].n * evalExpr(e2).asInstanceOf[NumVal].n)
    case Cat(e1, e2)    => StrVal(evalExpr(e1).asInstanceOf[StrVal].s + evalExpr(e2).asInstanceOf[StrVal].s)
    case Len(e1)        => NumVal(evalExpr(e1).asInstanceOf[StrVal].s.length)
    case Let(e1, x, e2) => evalExpr(subst(evalExpr(e1), x)(e2))
    case Lam(t, x, e)   => LamVal(t, x, e)
    case Ap(e1, e2) => {
      val lam = evalExpr(e1).asInstanceOf[LamVal]
      evalExpr(subst(evalExpr(e2), lam.x)(lam.e))
    }
  }

  private var varTag : Int = 0

  private def newVar : String = {
    varTag = varTag + 1
    "var-" + varTag
  }

  def subst(v : Value, x : String) : Expr => Expr = {
    case Var(y)        => if (x == y) v.toExpr else Var(y)
    case Str(s)        => Str(s)
    case Num(n)        => Num(n)
    case Plus(e1, e2)  => Plus(subst(v, x)(e1), subst(v, x)(e2))
    case Times(e1, e2) => Times(subst(v, x)(e1), subst(v, x)(e2))
    case Cat(e1, e2)   => Cat(subst(v, x)(e1), subst(v, x)(e2))
    case Len(e1)       => Len(subst(v, x)(e1))
    case Let(e1, y, e2) => {
      val nv = newVar
      Let(subst(v, x)(e1), nv, subst(v, x)(rename(y, nv)(e2)))
    }
    case Lam(t, y, e) => {
      val nv = newVar
      Lam(t, nv, subst(v, x)(rename(y, nv)(e)))
    }
    case Ap(e1, e2) => Ap(subst(v, x)(e1), subst(v, x)(e2))
  }

  def rename(x : String, y : String) : Expr => Expr = {
    case Var(z)        => if (z == x) Var(y) else Var(z)
    case Str(s)        => Str(s)
    case Num(n)        => Num(n)
    case Plus(e1, e2)  => Plus(rename(x, y)(e1), rename(x, y)(e2))
    case Times(e1, e2) => Times(rename(x, y)(e1), rename(x, y)(e2))
    case Cat(e1, e2)   => Cat(rename(x, y)(e1), rename(x, y)(e2))
    case Len(e1)       => Len(rename(x, y)(e1))
    case Let(e1, z, e2) => {
      val nv = newVar
      Let(rename(x, y)(e1), nv, rename(x, y)(rename(z, nv)(e2)))
    }
    case Lam(t, z, e) => {
      val nv = newVar
      Lam(t, nv, rename(x, y)(rename(z, nv)(e)))
    }
    case Ap(e1, e2) => Ap(rename(x, y)(e1), rename(x, y)(e2))
  }

}