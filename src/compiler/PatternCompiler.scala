package compiler

import model.{ ZVal, ZPat, WildPat, VarPat, Value, TrivVal, TrivPat, SVal, SPat, Rule, Pattern, PairVal, PairPat, InRVal, InRPat, InLVal, InLPat, Expr }

object PatternCompiler {

  var n : Int = 0

  def run(v1 : Value, rs : List[Rule]) : (Expr, Map[String, Value]) = {
    PatternCPU.run(v1, compileFullPattern(rs))
  }

  def compileFullPattern(rss : List[Rule]) : List[PatternOpcode] = compileRules(rss) ++ List(Label("donePattern"), Exit)

  def compileRules(rss : List[Rule]) : List[PatternOpcode] = rss match {
    case Nil => List(Thrw("No pattern match found"))
    case Rule(p, b) :: rs => {
      n = n + 1
      val failtag = "failure" + n
      List(ClearRetStack, ResetV) ++ compileRule(p, b, "donePattern", failtag) ++ List(Label(failtag)) ++ compileRules(rs)
    }
  }

  def compileRule(p : Pattern, b : Expr, succtag : String, failtag : String) : List[PatternOpcode] = p match {
    case WildPat    => List(NoRegPop, SetMatchRetval(Map()), SetRetval(b), Jump(succtag))
    case TrivPat    => List(PopLoadStack, SetMatchRetval(Map()), SetRetval(b), Jump(succtag))
    case VarPat(x)  => List(NoRegPop, AddMatchRetval(x), SetRetval(b), Jump(succtag))
    case ZPat       => List(PopLoadStack, JIfValtagNEq(0, failtag), SetMatchRetval(Map()), SetRetval(b), Jump(succtag))
    case SPat(sp)   => List(PopLoadStack, JIfValtagNEq(1, failtag)) ++ compileRule(sp, b, succtag, failtag)
    case InLPat(sp) => List(PopLoadStack, JIfValtagNEq(0, failtag)) ++ compileRule(sp, b, succtag, failtag)
    case InRPat(sp) => List(PopLoadStack, JIfValtagNEq(1, failtag)) ++ compileRule(sp, b, succtag, failtag)
    case PairPat(p1, p2) => {
      n = n + 1
      val subsucc1 = "success" + n
      val subOps1 = compileRule(p1, b, subsucc1, failtag)
      n = n + 1
      val subsucc2 = "success" + n
      val subOps2 = compileRule(p2, b, subsucc2, failtag)
      List(PopLoadStack) ++ subOps1 ++ List(Label(subsucc1), PushRetStack) ++ subOps2 ++ List(Label(subsucc2), PopRetStack, SetRetval(b), Jump(succtag))
    }
  }

}