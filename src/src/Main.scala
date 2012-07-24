package src

import reduct.Parserizer
import reduct.Typechecker
import reduct.Evaluator

object Main {

  def main(args : Array[String]) : Unit = {
    test("id(x : Nat) : Nat = x;"
       + "plus(a : Nat, b : Nat) : Nat = case a of {Z -> b | S(n) -> S(((plus n) b))};"
       + "times(a : Nat, b : Nat) : Nat = case a of {Z -> Z | S(n) -> ((plus b) ((times n) b))};"
       + "fact(n : Nat) : Nat = case n of {Z -> S(Z) | S(n) -> ((times S(n)) (fact n))};" 
       + "(fact S(S(S(S(Z)))))")
       
    test("swap(p : (Unit, Nat)) : (Nat, Unit) = case p of {(a, b) -> (b, a)};"
       + "null : Unit = ();"
       + "(swap (null, S(Z)))")
       
    test("swap(p : ((Unit, Nat), Nat)) : (Unit, (Nat, Nat)) = case p of {((a, b), c) -> (a, (b, c))};"
       + "null : Unit = ();"
       + "(swap ((null, S(Z)), S(S(Z))))")
       
    test("ifC(b : (Unit + Unit), e1 : Nat, e2 : Nat) : Nat = case b of{inl x -> e1 | inr x -> e2};"
       + "plus(a : Nat, b : Nat) : Nat = case a of {Z -> b | S(n) -> S(((plus n) b))};"
       + "((plus (((ifC inl () : (Unit + Unit)) S(Z)) Z)) (((ifC inr () : (Unit + Unit)) S(S(S(S(Z))))) S(S(Z))))")
       
    test("type Bool = (Unit + Unit);"
       + "true : Bool = inl () : Bool;"
       + "false : Bool = inr () : Bool;"
       + "plus(a : Nat, b : Nat) : Nat = case a of {Z -> b | S(n) -> S(((plus n) b))};"
       + "((plus if true then S(Z) else Z) if false then S(S(S(S(Z)))) else S(S(Z)))")
       
    test("case inr inl () : (Unit + Nat) : ((Nat, Nat) + (Unit + Nat)) of {"
       + "inl (S(_), y) -> y |"
       + "inl (Z, y) -> S(y) |"
       + "inr inl () -> S(S(Z)) |"
       + "inr inr x -> S(S(S(x))) }")
  }
  
  def test(progs : String) {
    println("prog\n" + progs + "\n")
    val prog = Parserizer.parse(progs)
    println("parse\n" + prog + "\n")
    println("type\n" + Typechecker.typecheck(prog).get + "\n")
    println("value\n" + Evaluator.evaluate(prog) + "\n")
    println("-----------------------------")
  }
  
}