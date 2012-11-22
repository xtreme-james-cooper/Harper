package compiler

import model.Expr
import model.Value
import model.TrivVal
import model.InLVal
import model.ZVal
import model.InRVal
import model.PairVal
import model.SVal
import model.FoldVal

object PatternCPU {

  var PC : Int = 0
  var prog : List[PatternOpcode] = null

  val register : Array[Int] = Array.ofDim(32)
  val R_TAG = 0
  val R_VAL_SP = 1
  val R_BIND_SP = 2
  val R_VAL_HP = 3

  val valStack : Array[HeapValue] = Array.ofDim(1000) //TODO large enough?
  val bindStack : Array[(String, HeapValue)] = Array.ofDim(1000) //TODO large enough?
  val valHeap : Array[HeapValue] = Array.ofDim(100000) //TODO large enough?
  
  var v : HeapValue = null

  var retval : Expr = null

  def run(v1 : Value, pr : List[PatternOpcode]) : (Expr, Map[String, Value]) = {
    PC = 0
    prog = SetReg(R_VAL_HP, 0) :: HeapPush(heapificate(v1)) :: pr

    prog.foreach(println)

    while (prog(PC) != Exit) {
      prog(PC).execute
      PC = PC + 1
    }

    (retval, Map() ++ (for {
      i <- 0 until register(R_BIND_SP)
      (s, h) = bindStack(i)
    } yield (s, unheap(h))))
  }

  case class HeapValue(tag : Int, a : HeapValue, b : HeapValue)

  val ZTAG = 0
  val TRIVTAG = 1
  val STAG = 2
  val INLTAG = 3
  val INRTAG = 4
  val FOLDTAG = 5
  val PAIRTAG = 6
  
  def heapificate(v : Value) : HeapValue = v match {
    case ZVal          => HeapValue(ZTAG, null, null)
    case SVal(a)       => HeapValue(STAG, heapificate(a), null)
    case InLVal(a)     => HeapValue(INLTAG, heapificate(a), null)
    case InRVal(a)     => HeapValue(INRTAG, heapificate(a), null)
    case TrivVal       => HeapValue(TRIVTAG, null, null)
    case PairVal(a, b) => HeapValue(PAIRTAG, heapificate(a), heapificate(b))
    case FoldVal(a)    => HeapValue(FOLDTAG, heapificate(a), null)
    case _             => throw new Exception("not possible in pattern matching!" + v)
  }

  def unheap(h : HeapValue) : Value = h match {
    case HeapValue(ZTAG, a, b) => ZVal
    case HeapValue(STAG, a, b) => SVal(unheap(a))
    case HeapValue(INLTAG, a, b) => InLVal(unheap(a))
    case HeapValue(INRTAG, a, b) => InRVal(unheap(a))
    case HeapValue(TRIVTAG, a, b) => TrivVal
    case HeapValue(PAIRTAG, a, b) => PairVal(unheap(a), unheap(b))
    case HeapValue(FOLDTAG, a, b) => FoldVal(unheap(a))
  }

}