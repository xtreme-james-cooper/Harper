package reduct

import model.{ ZVal, ZPat, WildPat, VarPat, Value, TrivVal, TrivPat, SVal, SPat, Rule, Pattern, PairVal, PairPat, InRVal, InRPat, InLVal, InLPat, Expr }

object PatternEvaluator extends Evaluator[PatStack, (Pattern, Value), Map[String, Value]] {

  //All these are init'd to null, because they are manually set in each pass
  //Conceptually, this is a tail-recursive state-machine; for efficiency reasons we actually modify vars, but it's not strictly necessary
  private var rules : List[Rule] = null //Rules as yet untried
  private var matchVal : Value = null //Value being matched against
  private var body : Expr = null //The body to be evaluated if the match succeeds

  def run(v : Value, p : Pattern, b : Expr, rs : List[model.Rule]) : (Expr, Map[String, Value]) = {
    rules = rs
    matchVal = v
    body = b

    loop((p, v))
    
    (body, target.asInstanceOf[Return[(Pattern, Value), Map[String, Value]]].v)
  }

  override def evalStep(e : (Pattern, Value)) : Unit = e match {
    case (WildPat, _)           => target = Return(Map())
    case (VarPat(x), v)         => target = Return(Map(x -> v))
    case (ZPat, ZVal)           => target = Return(Map())
    case (SPat(p), SVal(v))     => target = Eval(p, v)
    case (TrivPat, TrivVal)     => target = Return(Map())
    case (InLPat(p), InLVal(v)) => target = Eval(p, v)
    case (InRPat(p), InRVal(v)) => target = Eval(p, v)
    case (PairPat(p1, p2), PairVal(v1, v2)) => {
      push(PatStackLPair(v2, p2))
      target = Eval(p1, v1)
    }
    case _ => rules match { //Match failed; move on to the next pattern
      case Nil => throw new Exception("No pattern match found for " + matchVal)
      case Rule(p, b) :: rs => {
        rules = rs
        body = b
        stack = Nil //just ditch unmatched parts, since they're irrelevant
        target = Eval(p, matchVal)
      }
    }

  }

  override def returnStep(bind : Map[String, Value], s : PatStack) : Unit = s match {
    case PatStackLPair(v2, p2) => {
      push(PatStackRPair(bind))
      target = Eval(p2, v2)
    }
    case PatStackRPair(m1) if ((m1.keySet & bind.keySet).isEmpty) => target = Return(m1 ++ bind)
    //genuine error; as of now, no way to check
    case PatStackRPair(m1)                                        => throw new Exception("Patterns cannot have repeated variables") 

  }

  override def throwStep(s : String) : Unit =
    throw new Exception("Unexpected throw " + s + " in pattern matcher") //Should not happen

}