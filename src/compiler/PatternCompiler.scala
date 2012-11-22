package compiler

import model.{ ZVal, ZPat, WildPat, VarPat, Value, TrivVal, TrivPat, SVal, SPat, Rule, Pattern, PairVal, PairPat, InRVal, InRPat, InLVal, InLPat, Expr }

object PatternCompiler {
  
  def run(v1 : Value, rs : List[Rule]) : (Expr, Map[String, Value]) = {
    PatternCPU.run(v1, compileRules(rs).toArray)
  }

  def compileRules(rss : List[Rule]) : List[PatternOpcode] = rss match {
    case Nil => List(Thrw("No pattern match found"))
    case Rule(p, b) :: rs => List(RunRules(rss), Exit) //compileRule(p, b) ++ compileRules(rs)
  }
  
  def runRules(rs : List[Rule]) : (Expr, Map[String, Value]) = rs match {
    case Nil => throw new Exception("No pattern match found for " + PatternCPU.v)
    case Rule(p, b) :: rs => {
      val (isMatched, bind) = runMatch(p, null)
      if (isMatched)
        (b, bind)
      else
        runRules(rs)
    }
  }

  def runMatch(p : Pattern, retval : Map[String, Value]) : (Boolean, Map[String, Value]) = p match {
    case WildPat   => (true, Map())
    case TrivPat   => (true, Map())
    case VarPat(x) => (true, Map(x -> PatternCPU.v))
    case ZPat      => if (PatternCPU.v == ZVal) (true, Map()) else (false, null)
    case SPat(p) => PatternCPU.v match {
      case SVal(v1) => {
        SetV(v1).execute
        runMatch(p, null)
      }
      case _       => (false, null)
    }
    case InLPat(p) => PatternCPU.v match {
      case InLVal(v1) => {
        SetV(v1).execute
        runMatch(p, null)
      }
      case _         => (false, null)
    }
    case InRPat(p) => PatternCPU.v match {
      case InRVal(v1) => {
        SetV(v1).execute
        runMatch(p, null)
      }
      case _         => (false, null)
    }
    case PairPat(p1, p2) => PatternCPU.v match {
      case PairVal(v1, v2) => {
        SetV(v1).execute
        val (iMat, retv) = runMatch(p1, null)
        if (iMat) {
          SetV(v2).execute
          val (imat2, retv2) = runMatch(p2, null)
          if (imat2)
            (true, retv ++ retv2)
          else
            (false, null)
        } else
          (false, null)
      }
      case _ => throw new Exception("type error!")
    }
  }

}