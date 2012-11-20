package model

sealed abstract class Expr(name : String) {
  override def toString : String = name

  //expand type synonyms in tyenv
  def typeExpand(tyenv : Map[String, Type]) : Expr = this match {
    //Safe to ignore bindings in Fold and TyLam because TySyns must be uppercase strings and TyVars must be lowercase
    case Var(x)         => Var(x)
    case Z              => Z
    case S(n)           => S(n.typeExpand(tyenv))
    case Lam(v, t, e)   => Lam(v, t.swap(tyenv), e.typeExpand(tyenv))
    case App(e1, e2)    => App(e1.typeExpand(tyenv), e2.typeExpand(tyenv))
    case Fix(v, t, e)   => Fix(v, t.swap(tyenv), e.typeExpand(tyenv))
    case Triv           => Triv
    case PairEx(e1, e2) => PairEx(e1.typeExpand(tyenv), e2.typeExpand(tyenv))
    case InL(e)         => InL(e.typeExpand(tyenv))
    case InR(e)         => InR(e.typeExpand(tyenv))
    case Match(e, rs)   => Match(e.typeExpand(tyenv), rs.map({ case Rule(p, b) => Rule(p, b.typeExpand(tyenv)) }))
    case Fold(mu, t, e) => Fold(mu, t.swap(tyenv), e.typeExpand(tyenv))
    case Unfold(e)      => Unfold(e.typeExpand(tyenv))
    case TypeLam(t, e)  => TypeLam(t, e.typeExpand(tyenv))
    case TypeApp(e, t)  => TypeApp(e.typeExpand(tyenv), t.swap(tyenv))
  }

}

case class Var(v : String) extends Expr(v)
case object Z extends Expr("Z")
case class S(e : Expr) extends Expr("S(" + e + ")")
case class Lam(v : String, t : Type, e : Expr) extends Expr("\\" + v + " . " + e)
case class App(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + " " + e2 + ")")
case class Fix(v : String, t : Type, e : Expr) extends Expr("fix " + v + " in " + e)
case object Triv extends Expr("()")
case class PairEx(e1 : Expr, e2 : Expr) extends Expr("(" + e1 + ", " + e2 + ")")
case class InL(i : Expr) extends Expr("inl " + i)
case class InR(i : Expr) extends Expr("inr " + i)
case class Match(t : Expr, rules : List[Rule]) extends Expr("case " + t + " of {" + rules.foldRight("")({ case (r1, r2) => r1 + " | " + r2 }) + "}")
case class Fold(mu : String, t : Type, e : Expr) extends Expr("fold " + e)
case class Unfold(e : Expr) extends Expr("unfold " + e)
case class TypeLam(t : String, e : Expr) extends Expr("/\\" + t + " . " + e)
case class TypeApp(e : Expr, t : Type) extends Expr("[" + e + " " + t + "]")
