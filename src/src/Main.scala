package src

import typechecker.ProgChecker
import interpreter.ProgEvaluator
import parser.ProgParser
import compiler.ProgCompiler

object Main {

  def main(args : Array[String]) : Unit = {

    test("return ()")

    test("null : Unit = (); return null")

    test("plus(a : Nat, b : Nat) : Nat = case a of {Z -> b | S(n) -> S(((plus n) b))}; return ((plus 2) 3)")

    test("swap(p : (Unit, Nat)) : (Nat, Unit) = case p of {(a, b) -> (b, a)};"
      + "null : Unit = ();"
      + "return (swap (null, S(Z)))")

    test("type UnNat = (Unit, Nat);"
      + "swap(p : UnNat) : (Nat, Unit) = case p of {(a, b) -> (b, a)};"
      + "null : Unit = ();"
      + "return (swap (null, S(Z)))")

    test("swap(p : ((Unit, Nat), Nat)) : (Unit, (Nat, Nat)) = case p of {((a, b), c) -> (a, (b, c))};"
      + "null : Unit = ();"
      + "return (swap ((null, S(Z)), 2))")

    test("ifC(b : Bool, e1 : Nat, e2 : Nat) : Nat = case b of{inl x -> e1 | inr x -> e2};"
      + "plus(a : Nat, b : Nat) : Nat = case a of {Z -> b | S(n) -> S(((plus n) b))};"
      + "return ((plus (((ifC true) S(Z)) Z)) (((ifC false) S(S(S(S(Z))))) S(S(Z))))")

    test("return case inr inl () of {"
      + "inl (S(_), y) -> y |"
      + "inl (Z, y) -> S(y) |"
      + "inr inl () -> 2 |"
      + "inr inr x -> S(S(S(x))) }")

    test("return case inr inr 5 of {"
      + "inl (S(_), y) -> y |"
      + "inl (Z, y) -> S(y) |"
      + "inr inl () -> 2 |"
      + "inr inr x -> S(S(S(x))) }")
      
    test("nil : mu t.(Unit + (Nat, t)) = fold t.(Unit + (Nat, t)) inl ();"
      + "cons(n : Nat, l : mu t.(Unit + (Nat, t))) : mu t.(Unit + (Nat, t)) = fold t.(Unit + (Nat, t)) inr(n, l);"
      + "listItem : mu t.(Unit + (Nat, t)) = ((cons 2) ((cons 3) nil));"
      + "return listItem")

    test("nil : mu t.(Unit + (Nat, t)) = fold t.(Unit + (Nat, t)) inl ();"
      + "cons(n : Nat, l : mu t.(Unit + (Nat, t))) : mu t.(Unit + (Nat, t)) = fold t.(Unit + (Nat, t)) inr(n, l);"
      + "listItem : mu t.(Unit + (Nat, t)) = ((cons 2) ((cons 3) nil));"
      + "length(l : mu t.(Unit + (Nat, t))) : Nat = case unfold l of { inl _ -> 0 | inr (_, l2) -> S((length l2)) };"
      + "return (length listItem)")

    //Test stack depth!
    test("id(x : Nat) : Nat = x;"
      + "plus(a : Nat, b : Nat) : Nat = case a of {Z -> b | S(n) -> S(((plus n) b))};"
      + "times(a : Nat, b : Nat) : Nat = case a of {Z -> Z | S(n) -> ((plus b) ((times n) b))};"
      + "fact(n : Nat) : Nat = case n of {Z -> 1 | S(n) -> ((times S(n)) (fact n))};"
      + "return (fact 6)")

    test("id : forall t.(t -> t) = /\\ t. \\x : t . x;"
      + "return (([id Nat] 5), ([id Unit] ()))")

    test("snd : forall a. forall b. ((a, b) -> b) = /\\ a. /\\b. \\x : (a, b) . case x of { (a, b) -> b };"
      + "return ([[snd Unit] Nat] ((), 2))")

    test("type List = mu t.(Unit + (Nat, t));"
        + "nil : List = fold k.(Unit + (Nat, k)) inl ();"
        + "cons(n : Nat, l : List) : List = fold b.(Unit + (Nat, b)) inr(n, l);"
        + "listItem : List = ((cons 2) ((cons 3) nil));"
        + "length(l : List) : Nat = case unfold l of { inl _ -> 0 | inr (_, l2) -> S((length l2)) };"
        + "return (length listItem)")

    test("ifC(b : Bool, e1 : (Nat -> Nat), e2 : (Nat -> Nat)) : Nat = case b of{inl x -> (e1 0) | inr x -> (e2 0)};"
        + "return (((ifC true) \\x:Nat . 3) \\x:Nat . throw bleh)")
  
    test("ifC(b : Bool, e1 : (Nat -> Nat), e2 : (Nat -> Nat)) : Nat = case b of{inl x -> (e1 0) | inr x -> (e2 0)};"
        + "return (((ifC false) \\x:Nat . 3) \\x:Nat . throw bleh)")
    
    test("ifC(b : Bool, e1 : (Nat -> Nat), e2 : (Nat -> Nat)) : Nat = case b of{inl x -> (e1 0) | inr x -> (e2 0)};"
        + "return try (((ifC true) \\x:Nat . 3) \\x:Nat . throw bleh) catch 2")
  
    test("ifC(b : Bool, e1 : (Nat -> Nat), e2 : (Nat -> Nat)) : Nat = case b of{inl x -> (e1 0) | inr x -> (e2 0)};"
        + "return try (((ifC false) \\x:Nat . 3) \\x:Nat . throw bleh) catch 2")

    test("return S(throw bleh)")
    
    test("a(b : Nat) : Nat = throw bleh;"
        + "return try (a 2) catch 4")
        
    test("plus(a : Nat, b : Nat) : Nat = case a of {Z -> b | S(n) -> S(((plus n) b))};"
        + "decl a := 0 in decl b := 3 in bind x <- command !b; a := ((plus x) 2); bind y <- command !a; return y")

    test("plus(a : Nat, b : Nat) : Nat = case a of {Z -> b | S(n) -> S(((plus n) b))};"
      + "sum(x : Nat, y : Nat) : Nat = decl a := ((plus x) y) in bind b <- command !a; return b;"
      + "decl a := 2 in decl b := 3 in bind aa <- command !a; bind bb <- command !b; bind x <- ((sum aa) bb); a := ((plus x) 1); bind y <- command !a; return y")
  }

  def test(progs : String) {
    println("prog" + ": " + progs)
    val prog = ProgParser.parse(progs)
    println("parse" + ": " + prog)
    println("type")
    for ((name, typ) <- ProgChecker.typeCheck(prog)) println(name + " : " + typ)
    val intVal = ProgEvaluator.run(prog)
    val compVal = ProgCompiler.run(prog)
    if (intVal.toString != compVal.toString) throw new Exception("values don't match! " + intVal + " " + compVal)
    println("value" + ": " + intVal)
    println("-----------------------------")

  }

}