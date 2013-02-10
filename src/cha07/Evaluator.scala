package cha07

object Evaluator {

  def evalExpr : Expr => Value = {
    case Var(x) => throw new Exception("unbound variable " + x)
    case Str(s) => StrVal(s)
    case Num(n) => NumVal(n)
    case Plus(e1, e2) => NumVal(evalExpr(e1).asInstanceOf[NumVal].n + evalExpr(e2).asInstanceOf[NumVal].n)
    case Times(e1, e2) => NumVal(evalExpr(e1).asInstanceOf[NumVal].n * evalExpr(e2).asInstanceOf[NumVal].n)
    case Cat(e1, e2) => StrVal(evalExpr(e1).asInstanceOf[StrVal].s + evalExpr(e2).asInstanceOf[StrVal].s)
    case Len(e1) => NumVal(evalExpr(e1).asInstanceOf[StrVal].s.length)
    case Let(e1, x, e2) => evalExpr(subst(evalExpr(e1), x)(e2))
  }
  
  def subst(v : Value, x : String) : Expr => Expr = {
    case Var(y) => if (x == y) v.toExpr else Var(y)
    case Str(s) => Str(s)
    case Num(n) => Num(n)
    case Plus(e1, e2) => Plus(subst(v, x)(e1), subst(v, x)(e2))
    case Times(e1, e2) => Times(subst(v, x)(e1), subst(v, x)(e2))
    case Cat(e1, e2) => Cat(subst(v, x)(e1), subst(v, x)(e2))
    case Len(e1) => Len(subst(v, x)(e1))
    case Let(e1, y, e2) => Let(subst(v, x)(e1), x, if (x == y) e2 else subst(v, x)(e2))
  }


}