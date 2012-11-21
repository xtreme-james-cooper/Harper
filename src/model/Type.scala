package model

sealed abstract class Type(name : => String) {
  override def toString : String = name

  //replace all type variables mu with x
  def swap(mu : String, x : Type) : Type = this match {
    case Nat                         => Nat
    case Arrow(t1, t2)               => Arrow(t1.swap(mu, x), t2.swap(mu, x))
    case UnitTy                      => UnitTy
    case Product(t1, t2)             => Product(t1.swap(mu, x), t2.swap(mu, x))
    case Sum(t1, t2)                 => Sum(t1.swap(mu, x), t2.swap(mu, x))
    case TyVar(y) if y == mu         => x
    case TyVar(y)                    => TyVar(y)
    case Inductive(y, t1) if y == mu => Inductive(y, t1)
    case Inductive(y, t1)            => Inductive(y, t1.swap(mu, x))
    case ForAll(y, t1) if y == mu    => ForAll(y, t1)
    case ForAll(y, t1)               => ForAll(y, t1.swap(mu, x))
    case Unknown(id)                 => Unknown(id)
    case CommandTy(t)                => CommandTy(t.swap(mu, x))
  }

  //replace unknown #i with x
  def swap(i : Int, x : Type) : Type = this match {
    case Nat                    => Nat
    case Arrow(t1, t2)          => Arrow(t1.swap(i, x), t2.swap(i, x))
    case UnitTy                 => UnitTy
    case Product(t1, t2)        => Product(t1.swap(i, x), t2.swap(i, x))
    case Sum(t1, t2)            => Sum(t1.swap(i, x), t2.swap(i, x))
    case TyVar(y)               => TyVar(y)
    case Inductive(y, t1)       => Inductive(y, t1.swap(i, x))
    case ForAll(y, t1)          => ForAll(y, t1.swap(i, x))
    case Unknown(id) if i == id => x
    case Unknown(id)            => Unknown(id)
    case CommandTy(t)           => CommandTy(t.swap(i, x))
  }

  def swap(tyenv : Map[String, Type]) : Type = tyenv.foldLeft(this)({ case (t, (syn, x)) => t.swap(syn, x) })

  //Compares and builds contraints; also does alpha-renaming
  def ~=~(t2 : Type) : List[(Type, Type)] = (this, t2) match {
    case (Unknown(i), b)                        => (Unknown(i), b) :: Nil
    case (a, Unknown(i))                        => (Unknown(i), a) :: Nil
    case (Inductive(x, st1), Inductive(y, st2)) => st1 ~=~ st2.swap(y, TyVar(x))
    case (ForAll(x, st1), ForAll(y, st2))       => st1 ~=~ st2.swap(y, TyVar(x))
    case (Nat, Nat)                             => Nil
    case (CommandTy(t1), CommandTy(t2))         => t1 ~=~ t2
    case (Arrow(t1, t2), Arrow(t3, t4))         => t1 ~=~ t3 ++ t2 ~=~ t4
    case (UnitTy, UnitTy)                       => Nil
    case (Product(t1, t2), Product(t3, t4))     => t1 ~=~ t3 ++ t2 ~=~ t4
    case (Sum(t1, t2), Sum(t3, t4))             => t1 ~=~ t3 ++ t2 ~=~ t4
    case (TyVar(x), TyVar(y)) if x == y         => Nil
    case (_, _)                                 => throw new Exception("Cannot match " + this + " and " + t2)
  }

}

case object Nat extends Type("Nat")
case class Arrow(t1 : Type, t2 : Type) extends Type("(" + t1 + " -> " + t2 + ")")
case object UnitTy extends Type("Unit")
case class Product(t1 : Type, t2 : Type) extends Type("(" + t1 + ", " + t2 + ")")
case class Sum(t1 : Type, t2 : Type) extends Type("(" + t1 + " + " + t2 + ")")
case class TyVar(t : String) extends Type(t)
case class Inductive(x : String, t : Type) extends Type("mu " + x + "." + t)
case class ForAll(x : String, t : Type) extends Type("forall " + x + "." + t)
case class CommandTy(t : Type) extends Type("IO " + t)

//Cannot be written and should not appear in the final result; just for type inference
case class Unknown(id : Int) extends Type("unknown " + id + " being used")
