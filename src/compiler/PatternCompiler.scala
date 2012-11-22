package compiler

import model.{ ZVal, ZPat, WildPat, VarPat, Value, TrivVal, TrivPat, SVal, SPat, Rule, Pattern, PairVal, PairPat, InRVal, InRPat, InLVal, InLPat, Expr }

object PatternCompiler {

  var n : Int = 0
  
  def run(v1 : Value, rs : List[Rule]) : (Expr, Map[String, Value]) = {
    PatternCPU.run(v1, compileFullPattern(rs).toArray)
  }

  def compileFullPattern(rss : List[Rule]) : List[PatternOpcode] = compileRules(rss) ++ List(Label("donePattern"), Exit)

  def compileRules(rss : List[Rule]) : List[PatternOpcode] = rss match {
    case Nil              => List(Thrw("No pattern match found"))
    case Rule(p, b) :: rs => compileRule(p, b) ++ compileRules(rs)
  }

  def compileRule(p : Pattern, b : Expr) : List[PatternOpcode] = p match {
    case WildPat         => List(SetMatchRetval(Map()), SetRetval(b), Jump("donePattern"))
    case TrivPat         => List(SetMatchRetval(Map()), SetRetval(b), Jump("donePattern"))
    case VarPat(x)       => List(AddMatchRetval(x), SetRetval(b), Jump("donePattern"))
    case ZPat            => {
      n = n + 1
      List(JIfNZ("subpattern" + n), SetMatchRetval(Map()), SetRetval(b), Jump("donePattern"), Label("subpattern" + n)) //TODO
    }
    case SPat(sp)        => List(RunMatch(p), SetRetval(b), JIfIsEvB("donePattern")) //TODO
    case InLPat(sp)      => List(RunMatch(p), SetRetval(b), JIfIsEvB("donePattern")) //TODO
    case InRPat(sp)      => List(RunMatch(p), SetRetval(b), JIfIsEvB("donePattern")) //TODO
    case PairPat(p1, p2) => List(RunMatch(p), SetRetval(b), JIfIsEvB("donePattern")) //TODO
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
      case _ => (false, null)
    }
    case InLPat(p) => PatternCPU.v match {
      case InLVal(v1) => {
        SetV(v1).execute
        runMatch(p, null)
      }
      case _ => (false, null)
    }
    case InRPat(p) => PatternCPU.v match {
      case InRVal(v1) => {
        SetV(v1).execute
        runMatch(p, null)
      }
      case _ => (false, null)
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