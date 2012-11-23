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
  val R_HEAP_A = 1
  val R_HEAP_B = 2
  val R_VAL_SP = 3
  val R_BIND_SP = 4
  val R_VAL_HP = 5

  val valStack : Array[HeapValue] = Array.ofDim(1000) //TODO large enough?
  val bindStack : Array[(String, HeapValue)] = Array.ofDim(1000) //TODO large enough?
  val valHeap : Array[HeapValue] = Array.ofDim(100000) //TODO large enough?

  var retval : Expr = null

  def run(v1 : Value, pr : List[PatternOpcode]) : (Expr, Map[String, Value]) = {
    PC = 0
    register(R_VAL_HP) = 0
    heapUp(v1)

    prog = pr

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

  case class HeapValue(tag : Int, a : Int, b : Int)

  val ZTAG = 0
  val TRIVTAG = 1
  val STAG = 2
  val INLTAG = 3
  val INRTAG = 4
  val FOLDTAG = 5
  val PAIRTAG = 6

  def unheap(h : HeapValue) : Value = h match {
    case HeapValue(ZTAG, _, _)    => ZVal
    case HeapValue(TRIVTAG, _, _) => TrivVal
    case HeapValue(STAG, a, _)    => SVal(unheap(valHeap(a)))
    case HeapValue(INLTAG, a, _)  => InLVal(unheap(valHeap(a)))
    case HeapValue(INRTAG, a, _)  => InRVal(unheap(valHeap(a)))
    case HeapValue(FOLDTAG, a, _) => FoldVal(unheap(valHeap(a)))
    case HeapValue(PAIRTAG, a, b) => PairVal(unheap(valHeap(a)), unheap(valHeap(b)))
  }

  def heapUp(v : Value) : Int = {
    val ix = register(R_VAL_HP)
    register(R_VAL_HP) = register(R_VAL_HP) + 1
    valHeap(ix) = v match {
      case ZVal          => HeapValue(ZTAG, -1, -1)
      case TrivVal       => HeapValue(TRIVTAG, -1, -1)
      case SVal(a)       => HeapValue(STAG, heapUp(a), -1)
      case InLVal(a)     => HeapValue(INLTAG, heapUp(a), -1)
      case InRVal(a)     => HeapValue(INRTAG, heapUp(a), -1)
      case FoldVal(a)    => HeapValue(FOLDTAG, heapUp(a), -1)
      case PairVal(a, b) => HeapValue(PAIRTAG, heapUp(a), heapUp(b))
      case _             => throw new Exception("not possible in pattern matching!" + v)
    }
    ix
  }

}