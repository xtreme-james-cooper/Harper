package src

import interpreter.{ Typechecker, Evaluator }
import compiler.StackEval
import compiler.StateMachine
import model.{ Z, Unitt, Type, TyVar, Triv, Sum, S, Rec, Prod, Pairr, Nat, Expr, Arr }
import parser.ProgParser
import model.UncaughtException

object Main {

  def main(args : Array[String]) : Unit = {

    test("Z", Nat, Z)
    test("S(S(Z))", Nat, S(S(Z)))
    test("case S(Z) of {Z => Z; S(k) => S(S(k))}", Nat, S(S(Z)))
    test("(\\x:Nat.x S(Z))", Nat, S(Z))
    test("fix double:(Nat=>Nat) in \\x:Nat.case x of {Z => Z; S(k) => S(S((double k)))}", Arr(Nat, Nat))
    test("(fix double:(Nat=>Nat) in \\x:Nat.case x of {Z => Z; S(k) => S(S((double k)))} S(S(S(Z))))", Nat, S(S(S(S(S(S(Z)))))))
    test("(\\x:Unit.Z ())", Nat, Z)
    test("(fix swap:((Nat, Unit)=>(Unit, Nat)) in \\x:(Nat, Unit) . (projR x, projL x) (S(S(Z)), ()))", Prod(Unitt, Nat), Pairr(Triv, S(S(Z))))
    test("(\\x:(Unit+Nat).case x of {inL x => Z; inR x => S(x)} inL:(Unit+Nat) () )", Nat, Z)
    test("(\\x:(Unit+Nat).case x of {inL x => Z; inR x => S(x)} inR:(Unit+Nat) S(Z))", Nat, S(S(Z)))
    test("case (S(Z), inL : (Unit+Nat) ()) of { (n, inL _) => S(S(n)) ; (S(Z), inR Z) => Z }", Nat, S(S(S(Z))))
    test("case (S(Z), inR : (Unit+Nat) Z) of { (n, inL _) => S(S(n)) ; (S(Z), inR Z) => Z }", Nat, Z)
    test("fix length:(mu t.(Unit+(Nat, t)) => Nat) in \\l:mu t.(Unit+(Nat, t)).case unfold l of { inL () => Z ; inR (n, l) => S((length l)) }",
      Arr(Rec("t", Sum(Unitt, Prod(Nat, TyVar("t")))), Nat))
    test("let nil = fold:t.(Unit+(Nat, t)) inL:(Unit+(Nat,mu t.(Unit+(Nat, t)))) () in " +
      "let cons = \\h:Nat . \\t:mu t.(Unit+(Nat, t)) . fold:t.(Unit+(Nat, t)) inR:(Unit+(Nat,mu t.(Unit+(Nat, t)))) (h, t) in " +
      "let length = fix length:(mu t.(Unit+(Nat, t)) => Nat) in \\l:mu t.(Unit+(Nat, t)).case unfold l of { inL () => Z ; inR (n, l) => S((length l)) } in " +
      "(length ((cons Z) ((cons Z) nil)))", Nat, S(S(Z)))
    test("let id = /\\t.\\x:t.x in (([id Nat] Z), ([id Unit] ()))", Prod(Nat, Unitt), Pairr(Z, Triv))
    test("try Z catch S(Z)", Nat, Z)
    test("try raise:Nat catch S(Z)", Nat, S(Z))
    test("let fail = \\x:Unit . raise:Nat in " +
      "let baddub = fix double:(Nat=>Nat) in \\x:Nat.case x of {Z => (fail ()); S(k) => S(S((double k)))} in " +
      "(baddub S(Z))", Nat, UncaughtException)
    test("let fail = \\x:Unit . raise:Nat in " +
      "let baddub = fix double:(Nat=>Nat) in \\x:Nat.case x of {Z => (fail ()); S(k) => S(S((double k)))} in " +
      "try (baddub S(Z)) catch S(S(S(Z)))", Nat, S(S(S(Z))))
    test("try raise:Nat catch raise:Nat", Nat, UncaughtException)
    test("try abort:Nat raise:Void catch Z", Nat, Z)
  }

  def test(progs : String, eType : Type) : Unit = test(progs, eType, None)
  def test(progs : String, eType : Type, eVal : Expr) : Unit = test(progs, eType, Some(eVal))
  def test(progs : String, eType : Type, eVal : Option[Expr]) : Unit = {
    println("prog: " + progs)
    val prog = ProgParser.parse(progs)
    println("parse: " + prog)
    val typ = Typechecker.typecheck(prog)
    if (typ != eType) throw new Exception("expected " + eType + " but got " + typ)
    println("type: " + typ)
    val intVal = Evaluator.eval(prog)
    if (eVal.isDefined && intVal != eVal.get) throw new Exception("for interpreted expected " + eVal.get + " but got " + intVal)
    val stackVal = StackEval.eval(prog)
    if (eVal.isDefined && stackVal != eVal.get) throw new Exception("for stack expected " + eVal.get + " but got " + stackVal)
    val compVal = StateMachine.eval(prog)
    if (eVal.isDefined && compVal != eVal.get) throw new Exception("for compiled expected " + eVal.get + " but got " + compVal)
    if (eVal.isDefined && (stackVal != intVal || compVal != intVal || stackVal != compVal)) 
      throw new Exception("interpreted " + intVal + " stack " + stackVal + " compiled " + compVal)
    println("value" + ": " + intVal)
    println("-----------------------------")
  }

}