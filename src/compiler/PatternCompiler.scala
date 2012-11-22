package compiler

import model.{ ZVal, ZPat, WildPat, VarPat, Value, TrivVal, TrivPat, SVal, SPat, Rule, Pattern, PairVal, PairPat, InRVal, InRPat, InLVal, InLPat, Expr }

object PatternCompiler {

  var v : Value = null
  
  def run(v1 : Value, rs : List[Rule]) : (Expr, Map[String, Value]) = {
    v = v1
    runRules(rs)
  }

  def runRules(rs : List[Rule]) : (Expr, Map[String, Value]) = rs match {
    case Nil => throw new Exception("No pattern match found for " + v)
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
    case VarPat(x) => (true, Map(x -> v))
    case ZPat      => if (v == ZVal) (true, Map()) else (false, null)
    case SPat(p) => v match {
      case SVal(v1) => {
        v = v1
        runMatch(p, null)
      }
      case _       => (false, null)
    }
    case InLPat(p) => v match {
      case InLVal(v1) => {
        v = v1
        runMatch(p, null)
      }
      case _         => (false, null)
    }
    case InRPat(p) => v match {
      case InRVal(v1) => {
        v = v1
        runMatch(p, null)
      }
      case _         => (false, null)
    }
    case PairPat(p1, p2) => v match {
      case PairVal(v1, v2) => {
        v = v1
        val (iMat, retv) = runMatch(p1, null)
        if (iMat) {
          v = v2
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