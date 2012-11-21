package src

import reduct.Parserizer
import reduct.Typechecker
import reduct.Evaluator

object Main {

  def main(args : Array[String]) : Unit = {

    test("()")

    test("null : Unit = (); null")

    test("plus(a : Nat, b : Nat) : Nat = case a of {Z -> b | S(n) -> S(((plus n) b))}; ((plus 2) 3)")

    test("swap(p : (Unit, Nat)) : (Nat, Unit) = case p of {(a, b) -> (b, a)};"
      + "null : Unit = ();"
      + "(swap (null, S(Z)))")

    test("type UnNat = (Unit, Nat);"
      + "swap(p : UnNat) : (Nat, Unit) = case p of {(a, b) -> (b, a)};"
      + "null : Unit = ();"
      + "(swap (null, S(Z)))")

    test("swap(p : ((Unit, Nat), Nat)) : (Unit, (Nat, Nat)) = case p of {((a, b), c) -> (a, (b, c))};"
      + "null : Unit = ();"
      + "(swap ((null, S(Z)), 2))")

    test("ifC(b : Bool, e1 : Nat, e2 : Nat) : Nat = case b of{inl x -> e1 | inr x -> e2};"
      + "plus(a : Nat, b : Nat) : Nat = case a of {Z -> b | S(n) -> S(((plus n) b))};"
      + "((plus (((ifC true) S(Z)) Z)) (((ifC false) S(S(S(S(Z))))) S(S(Z))))")

    test("case inr inl () of {"
      + "inl (S(_), y) -> y |"
      + "inl (Z, y) -> S(y) |"
      + "inr inl () -> 2 |"
      + "inr inr x -> S(S(S(x))) }")

    test("nil : mu t.(Unit + (Nat, t)) = fold t.(Unit + (Nat, t)) inl ();"
      + "cons(n : Nat, l : mu t.(Unit + (Nat, t))) : mu t.(Unit + (Nat, t)) = fold t.(Unit + (Nat, t)) inr(n, l);"
      + "listItem : mu t.(Unit + (Nat, t)) = ((cons 2) ((cons 3) nil));"
      + "listItem")

    test("nil : mu t.(Unit + (Nat, t)) = fold t.(Unit + (Nat, t)) inl ();"
      + "cons(n : Nat, l : mu t.(Unit + (Nat, t))) : mu t.(Unit + (Nat, t)) = fold t.(Unit + (Nat, t)) inr(n, l);"
      + "listItem : mu t.(Unit + (Nat, t)) = ((cons 2) ((cons 3) nil));"
      + "length(l : mu t.(Unit + (Nat, t))) : Nat = case unfold l of { inl _ -> 0 | inr (_, l2) -> S((length l2)) };"
      + "(length listItem)")

    //Test stack depth!
    test("id(x : Nat) : Nat = x;"
      + "plus(a : Nat, b : Nat) : Nat = case a of {Z -> b | S(n) -> S(((plus n) b))};"
      + "times(a : Nat, b : Nat) : Nat = case a of {Z -> Z | S(n) -> ((plus b) ((times n) b))};"
      + "fact(n : Nat) : Nat = case n of {Z -> 1 | S(n) -> ((times S(n)) (fact n))};"
      + "(fact 6)")

    test("id : forall t.(t -> t) = /\\ t. \\x : t . x;"
      + "(([id Nat] 5), ([id Unit] ()))")

    test("snd : forall a. forall b. ((a, b) -> b) = /\\ a. /\\b. \\x : (a, b) . case x of { (a, b) -> b };"
      + "([[snd Unit] Nat] ((), 2))")

    test("type List = mu t.(Unit + (Nat, t));"
        + "nil : List = fold k.(Unit + (Nat, k)) inl ();"
        + "cons(n : Nat, l : List) : List = fold b.(Unit + (Nat, b)) inr(n, l);"
        + "listItem : List = ((cons 2) ((cons 3) nil));"
        + "length(l : List) : Nat = case unfold l of { inl _ -> 0 | inr (_, l2) -> S((length l2)) };"
        + "(length listItem)")

    test("ifC(b : Bool, e1 : (Nat -> Nat), e2 : (Nat -> Nat)) : Nat = case b of{inl x -> (e1 0) | inr x -> (e2 0)};"
        + "(((ifC true) \\x:Nat . 3) \\x:Nat . throw bleh)")
  
    test("ifC(b : Bool, e1 : (Nat -> Nat), e2 : (Nat -> Nat)) : Nat = case b of{inl x -> (e1 0) | inr x -> (e2 0)};"
        + "(((ifC false) \\x:Nat . 3) \\x:Nat . throw bleh)")
    
    test("ifC(b : Bool, e1 : (Nat -> Nat), e2 : (Nat -> Nat)) : Nat = case b of{inl x -> (e1 0) | inr x -> (e2 0)};"
        + "try (((ifC true) \\x:Nat . 3) \\x:Nat . throw bleh) catch 2")
  
    test("ifC(b : Bool, e1 : (Nat -> Nat), e2 : (Nat -> Nat)) : Nat = case b of{inl x -> (e1 0) | inr x -> (e2 0)};"
        + "try (((ifC false) \\x:Nat . 3) \\x:Nat . throw bleh) catch 2")

  }

  def printTest(name : String, value : Any) : Unit = {
    println(name)
    println(value.toString)
    println
  }

  def test(progs : String) {
    printTest("prog", progs)
    val prog = Parserizer.parse(progs)
    printTest("parse", prog)
    println("type")
    for ((name, typ) <- Typechecker.typecheck(prog)) println(name + " : " + typ)
    println
    printTest("value", Evaluator.evaluate(prog))
    println("-----------------------------")

  }

}