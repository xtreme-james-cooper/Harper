package compiler

import model.Expr

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
  val R_DUMMY = 31

  val valStack : Array[Int] = Array.ofDim(10000) //TODO large enough?
  val bindStack : Array[(String, (Int, Int, Int))] = Array.ofDim(100) //Should never have 100 bindings from a pattern
  val valHeap : Array[Int] = Array.ofDim(100000) //TODO large enough?

  var retval : String = null

  def run(v1 : Value, pr : List[PatternOpcode]) : (String, Map[String, Value]) = {
    PC = 0
    register(R_VAL_HP) = 0
    heapUp(v1)

    prog = pr

    //    prog.foreach(println)

    while (prog(PC) != Exit) {
      prog(PC).execute
      PC = PC + 1
    }

    (retval, Map() ++ (for {
      i <- 0 until register(R_BIND_SP)
      (s, h) = bindStack(i)
    } yield (s, unheap(h))))
  }

  def goto(l : String) : Unit = { //TODO do search better
    PC = 0
    while (prog(PC) != Label(l)) {
      PC = PC + 1
    }
  }

  case class HeapValue(tag : Int, a : Int, b : Int)

  val ZTAG = 0
  val TRIVTAG = 1
  val STAG = 2
  val INLTAG = 3
  val INRTAG = 4
  val FOLDTAG = 5
  val PAIRTAG = 6

  def unheap(h : (Int, Int, Int)) : Value = h match {
    case (ZTAG, _, _)    => ZVal
    case (TRIVTAG, _, _) => TrivVal
    case (STAG, a, _)    => SVal(unheap((valHeap(a), valHeap(a + 1), valHeap(a + 2))))
    case (INLTAG, a, _)  => InLVal(unheap((valHeap(a), valHeap(a + 1), valHeap(a + 2))))
    case (INRTAG, a, _)  => InRVal(unheap((valHeap(a), valHeap(a + 1), valHeap(a + 2))))
    case (FOLDTAG, a, _) => FoldVal(unheap((valHeap(a), valHeap(a + 1), valHeap(a + 2))))
    case (PAIRTAG, a, b) => PairVal(unheap((valHeap(a), valHeap(a + 1), valHeap(a + 2))), unheap((valHeap(b), valHeap(b + 1), valHeap(b + 2))))
  }

  def heapUp(v : Value) : Int = {
    val ix = register(R_VAL_HP)
    register(R_VAL_HP) = register(R_VAL_HP) + 3
    valHeap(ix) = v match {
      case ZVal          => ZTAG
      case TrivVal       => TRIVTAG
      case SVal(a)       => STAG
      case InLVal(a)     => INLTAG
      case InRVal(a)     => INRTAG
      case FoldVal(a)    => FOLDTAG
      case PairVal(a, b) => PAIRTAG
      case _             => throw new Exception("not possible in pattern matching!" + v)
    }
    valHeap(ix + 1) = v match {
      case SVal(a)       => heapUp(a)
      case InLVal(a)     => heapUp(a)
      case InRVal(a)     => heapUp(a)
      case FoldVal(a)    => heapUp(a)
      case PairVal(a, b) => heapUp(a)
      case _             => -1
    }
    valHeap(ix + 2) = v match {
      case PairVal(a, b) => heapUp(b)
      case _             => -1
    }
    ix
  }

}