package compiler

import model.{ ZPat, WildPat, VarPat, TrivPat, SPat, Rule, Pattern, PairPat, InRPat, InLPat, Expr }
import PatternCPU._

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
      List(SetReg(R_BIND_SP, 0), SetReg(R_VAL_SP, 0), SetReg(R_DUMMY, 0)) ++ pushVal(R_DUMMY) ++
        compileRule(p, b, "donePattern", failtag) ++ List(Label(failtag)) ++ compileRules(rs)
    }
  }

  def pushVal(reg : Int) : List[PatternOpcode] = List(ValPush(reg), Add1(reg), ValPush(reg), Add1(reg), ValPush(reg))

  def compileRule(p : Pattern, b : Expr, succtag : String, failtag : String) : List[PatternOpcode] = {
    val vintoFlag = "heaping" + n
    n = n + 1
    val putVIntoRegs = List(JIfLEq(R_TAG, TRIVTAG, vintoFlag)) ++ pushVal(R_HEAP_A) ++
      List(JIfLEq(R_TAG, FOLDTAG, vintoFlag)) ++ pushVal(R_HEAP_B) ++ List(Label(vintoFlag))
   
    List(ValPop(R_HEAP_B), ValPop(R_HEAP_A), ValPop(R_TAG)) ++ (p match {
      case WildPat    => List(SetRetval(b), Jump(succtag))
      case TrivPat    => putVIntoRegs ++ List(SetRetval(b), Jump(succtag))
      case VarPat(x)  => List(PushVRetStack(x), SetRetval(b), Jump(succtag))
      case ZPat       => putVIntoRegs ++ List(JIfNEq(R_TAG, ZTAG, failtag), SetRetval(b), Jump(succtag))
      case SPat(sp)   => putVIntoRegs ++ List(JIfNEq(R_TAG, STAG, failtag)) ++ compileRule(sp, b, succtag, failtag)
      case InLPat(sp) => putVIntoRegs ++ List(JIfNEq(R_TAG, INLTAG, failtag)) ++ compileRule(sp, b, succtag, failtag)
      case InRPat(sp) => putVIntoRegs ++ List(JIfNEq(R_TAG, INRTAG, failtag)) ++ compileRule(sp, b, succtag, failtag)
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