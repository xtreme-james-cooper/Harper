package compiler

import model.{ ZVal, ZPat, WildPat, VarPat, Value, TrivVal, TrivPat, SVal, SPat, Rule, Pattern, PairVal, PairPat, InRVal, InRPat, InLVal, InLPat, Expr }

object PatternCompiler { //extends Compiler[PatStack, (Pattern, Value), Map[String, Value]] {

  type Env = List[Map[String, Value]] //Not V, specifically Value

  private var rules : List[Rule] = null //Rules as yet untried
  private var matchVal : Value = null //Value being matched against
  private var body : Expr = null //The body to be evaluated if the match succeeds

  sealed abstract class Target
  case class Eval(e : (Pattern, Value)) extends Target
  case class Return(v : Map[String, Value]) extends Target

  def runRules(v : Value, rs : List[Rule]) : (Expr, Map[String, Value]) = rs match {
    case Nil => throw new Exception("No pattern match found for " + matchVal)
    case Rule(p, b) :: rs => {
      rules = rs
      matchVal = v
      body = b
      runMatch(Eval(p, v), Nil)
    }
  }

  def runMatch(target : Target, stack : List[PatStack]) : (Expr, Map[String, Value]) = target match {
    case Eval(e) => e match {
      case (WildPat, _)                       => runMatch(Return(Map()), stack)
      case (VarPat(x), v)                     => runMatch(Return(Map(x -> v)), stack)
      case (ZPat, ZVal)                       => runMatch(Return(Map()), stack)
      case (SPat(p), SVal(v))                 => runMatch(Eval(p, v), stack)
      case (TrivPat, TrivVal)                 => runMatch(Return(Map()), stack)
      case (InLPat(p), InLVal(v))             => runMatch(Eval(p, v), stack)
      case (InRPat(p), InRVal(v))             => runMatch(Eval(p, v), stack)
      case (PairPat(p1, p2), PairVal(v1, v2)) => runMatch(Eval(p1, v1), PatStackLPair(v2, p2) :: stack)
      case _ => rules match { //Match failed; move on to the next pattern
        case Nil => throw new Exception("No pattern match found for " + matchVal)
        case Rule(p, b) :: rs => {
          rules = rs
          body = b
          runMatch(Eval(p, matchVal), Nil)
        }
      }
    }
    case Return(bind) => stack match {
      case Nil                        => (body, bind)
      case PatStackLPair(v2, p2) :: s => runMatch(Eval(p2, v2), PatStackRPair(bind) :: s)
      case PatStackRPair(m1) :: s     => runMatch(Return(m1 ++ bind), s)
    }
  }

}