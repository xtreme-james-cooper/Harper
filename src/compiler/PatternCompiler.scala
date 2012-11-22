package compiler

import model.{ ZVal, ZPat, WildPat, VarPat, Value, TrivVal, TrivPat, SVal, SPat, Rule, Pattern, PairVal, PairPat, InRVal, InRPat, InLVal, InLPat, Expr }

object PatternCompiler { //extends Compiler[PatStack, (Pattern, Value), Map[String, Value]] {

  type Env = List[Map[String, Value]]

  sealed abstract class Target
  case class Eval(e : (Pattern, Value)) extends Target
  case class Return(v : Map[String, Value]) extends Target

  def run(v : Value, rs : List[Rule]) : (Expr, Map[String, Value]) = {
    runRules(v, rs)
  }

  def runRules(v : Value, rs : List[Rule]) : (Expr, Map[String, Value]) = rs match {
    case Nil => throw new Exception("No pattern match found for " + v)
    case Rule(p, b) :: rs => {
      val (isMatched, bind) = runMatch(false, (p, v), null, Nil)
      if (isMatched)
        (b, bind)
      else
        runRules(v, rs)
    }
  }

  def runMatch(isMatched : Boolean, e : (Pattern, Value), retval : Map[String, Value], stack : List[PatStack]) : (Boolean, Map[String, Value]) =
    if (isMatched) stack match {
      case Nil                        => (true, retval)
      case PatStackLPair(v2, p2) :: s => runMatch(false, (p2, v2), null, PatStackRPair(retval) :: s)
      case PatStackRPair(m1) :: s     => runMatch(true, null, m1 ++ retval, s)
    }
    else e match {
      case (WildPat, _)                       => runMatch(true, null, Map(), stack)
      case (VarPat(x), v)                     => runMatch(true, null, Map(x -> v), stack)
      case (ZPat, ZVal)                       => runMatch(true, null, Map(), stack)
      case (SPat(p), SVal(v))                 => runMatch(false, (p, v), null, stack)
      case (TrivPat, TrivVal)                 => runMatch(true, null, Map(), stack)
      case (InLPat(p), InLVal(v))             => runMatch(false, (p, v), null, stack)
      case (InRPat(p), InRVal(v))             => runMatch(false, (p, v), null, stack)
      case (PairPat(p1, p2), PairVal(v1, v2)) => runMatch(false, (p1, v1), null, PatStackLPair(v2, p2) :: stack)
      case _                                  => (false, null)
    }

}