package compiler

import model.{ ZPat, WildPat, VarPat, Value, TrivPat, SPat, Rule, Pattern, PairPat, InRPat, InLPat, Expr }

object PatternCompiler {

  var n : Int = 0

  def run(v1 : Value, rs : List[Rule]) : (Expr, Map[String, Value]) = {
    n = 0
    PatternCPU.run(v1, compileFullPattern(rs))
  }

  def compileFullPattern(rss : List[Rule]) : List[PatternOpcode] = compileRules(rss) ++ List(Label("donePattern"), Exit)

  def compileRules(rss : List[Rule]) : List[PatternOpcode] = rss match {
    case Nil => List(Thrw("No pattern match found"))
    case Rule(p, b) :: rs => {
      val failtag = "failure" + n
      n = n + 1
      List(SetReg(PatternCPU.R_BIND_SP, 0), SetReg(PatternCPU.R_VAL_SP, 0), ValPushC(0)) ++
        compileRule(p, b, "donePattern", failtag) ++ List(Label(failtag)) ++ compileRules(rs)
    }
  }

  def compileRule(p : Pattern, b : Expr, succtag : String, failtag : String) : List[PatternOpcode] = {
    val vintoFlag = "heaping" + n
    n = n + 1
    val putVIntoRegs = List(JIfLEq(PatternCPU.R_TAG, PatternCPU.TRIVTAG, vintoFlag), ValPushR(PatternCPU.R_HEAP_A), 
        JIfLEq(PatternCPU.R_TAG, PatternCPU.FOLDTAG, vintoFlag), ValPushR(PatternCPU.R_HEAP_B), Label(vintoFlag))
    List(ValPop) ++ (p match {
      case WildPat    => List(SetRetval(b), Jump(succtag))
      case TrivPat    => putVIntoRegs ++ List(SetRetval(b), Jump(succtag))
      case VarPat(x)  => List(PushVRetStack(x), SetRetval(b), Jump(succtag))
      case ZPat       => putVIntoRegs ++ List(JIfNEq(PatternCPU.R_TAG, PatternCPU.ZTAG, failtag), SetRetval(b), Jump(succtag))
      case SPat(sp)   => putVIntoRegs ++ List(JIfNEq(PatternCPU.R_TAG, PatternCPU.STAG, failtag)) ++ compileRule(sp, b, succtag, failtag)
      case InLPat(sp) => putVIntoRegs ++ List(JIfNEq(PatternCPU.R_TAG, PatternCPU.INLTAG, failtag)) ++ compileRule(sp, b, succtag, failtag)
      case InRPat(sp) => putVIntoRegs ++ List(JIfNEq(PatternCPU.R_TAG, PatternCPU.INRTAG, failtag)) ++ compileRule(sp, b, succtag, failtag)
      case PairPat(p1, p2) => {
        val subsucc1 = "success" + n
        n = n + 1
        val subOps1 = compileRule(p2, b, subsucc1, failtag)
        val subsucc2 = "success" + n
        n = n + 1
        val subOps2 = compileRule(p1, b, subsucc2, failtag)
        putVIntoRegs ++ subOps1 ++ List(Label(subsucc1)) ++ subOps2 ++ List(Label(subsucc2), SetRetval(b), Jump(succtag))
      }
    })
  }

}