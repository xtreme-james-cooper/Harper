package reduct

import model.{ZVal, ZPat, WildPat, VarPat, Value, TrivVal, TrivPat, SVal, SPat, Rule, Pattern, PairVal, PairPat, InRVal, InRPat, InLVal, InLPat, Expr}

object PatternEvaluator {

  sealed abstract class MatchingTarget
  case class Against(p : Pattern, v : Value) extends MatchingTarget
  case class Return(b : Map[String, Value]) extends MatchingTarget

  private var rules : List[Rule] = null //Rules as yet untried
  private var matchVal : Value = null //Value being matched against
  private var body : Expr = null //The body to be evaluated if the match succeeds
  private var stack : List[PatStack] = null //The parts of the pattern still unmatched
  private var target : MatchingTarget = null //Either a pattern against a variable, or a binding being returned

  private def push(s : PatStack) : Unit = stack = s :: stack

  private def pop : PatStack = stack match {
    case Nil => throw new Exception("Should have aborted the pattern driver loop!") //This is the escape case
    case s :: stk => {
      stack = stk
      s
    }
  }
  
  def run(v : Value, p : Pattern, b : Expr, rs : List[model.Rule]) : (Expr, Map[String, Value]) = {
    rules = rs
    matchVal = v
    body = b
    stack = Nil
    target = Against(p, matchVal)

    while (!(target.isInstanceOf[Return] && stack.isEmpty)) {
      matchPattern
    }
    (body, target.asInstanceOf[Return].b)
  }

  private def matchPattern : Unit = target match {
    case Against(WildPat, _)           => target = Return(Map())
    case Against(VarPat(x), v)         => target = Return(Map(x -> v))
    case Against(ZPat, ZVal)           => target = Return(Map())
    case Against(SPat(p), SVal(v))     => target = Against(p, v)
    case Against(TrivPat, TrivVal)     => target = Return(Map())
    case Against(InLPat(p), InLVal(v)) => target = Against(p, v)
    case Against(InRPat(p), InRVal(v)) => target = Against(p, v)
    case Against(PairPat(p1, p2), PairVal(v1, v2)) => {
      push(PatStackLPair(v2, p2))
      target = Against(p1, v1)
    }
    case Against(_, _) => rules match { //Match failed; move on to the next pattern
      case Nil => throw new Exception("No pattern match found for " + matchVal)
      case Rule(p, b) :: rs => {
        rules = rs
        body = b
        stack = Nil //just ditch unmatched parts, since they're irrelevant
        target = Against(p, matchVal)
      }
    }
    case Return(bind) => pop match {
      case PatStackLPair(v2, p2) => {
        push(PatStackRPair(bind))
        target = Against(p2, v2)
      }
      case PatStackRPair(m1) if ((m1.keySet & bind.keySet).isEmpty) => target = Return(m1 ++ bind)
      case PatStackRPair(m1) => throw new Exception("Patterns cannot have repeated variables") //genuine error; as of now, no way to check
    }
  }

}