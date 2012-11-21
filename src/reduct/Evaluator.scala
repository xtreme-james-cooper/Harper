package reduct

import model.Expr
import model.Z
import model.S
import model.Var
import model.App
import model.Lam
import model.Fix
import model.Prog
import model.Triv
import model.PairEx
import model.InL
import model.InR
import model.UnitTy
import model.Defn
import model.ExprDefn
import model.Value
import model.Match
import model.Rule
import model.LamVal
import model.ZVal
import model.TrivVal
import model.SVal
import model.InLVal
import model.InRVal
import model.PairVal
import model.RecursiveLamVal
import model.Fold
import model.Unfold
import model.FoldVal
import model.TypeLam
import model.TypeApp
import model.TypeLam
import model.TypeDefn
import model.ExceptionValue
import model.ThrowEx
import model.TryCatch
import model.CommandExp
import model.Ret
import model.Bind
import model.Decl
import model.Get
import model.SetCmd
import model.Action
import model.Command
import model.Pattern
import model.ZPat
import model.SPat
import model.WildPat
import model.VarPat
import model.TrivPat
import model.InLPat
import model.InRPat
import model.PairPat

object Evaluator {

  /*
   * Expr
   */

  sealed abstract class Target
  case class Eval(e : Expr) extends Target
  case class Return(v : Value) extends Target
  case class Throw(s : String) extends Target

  //All these are init'd to null, because they are manually set in each pass
  //Conceptually, this is a tail-recursive state-machine; for efficiency reasons we actually modify vars, but it's not strictly necessary
  var target : Target = null //The expression being evaluated, the value being returned, or and Excpetion being thrown
  var stack : List[Stack] = null //The parts of the expression whose evaluation has been deferred
  var env : List[Map[String, Value]] = null //The stack of variable-binding frames

  def pushExprStack(s : Stack) : Unit = stack = s :: stack

  def popExprStack : Stack = stack match {
    case Nil => throw new Exception("Should have aborted the eval driver loop!") //This is the escape case
    case s :: stk => {
      stack = stk
      s
    }
  }

  def getBinding(x : String) : Value = innerGetBinding(env, x)
  def innerGetBinding(e : List[Map[String, Value]], x : String) : Value = e match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m(x)
    case m :: e                  => innerGetBinding(e, x)
  }

  //Crush the env down into a single stack frame for use as a closure
  def flattenEnv : Map[String, Value] = env.foldRight(Map[String, Value]())({ case (m1, m2) => m2 ++ m1 })

  def runEval(e : Expr, m : List[Map[String, Value]]) : Value = {
    target = Eval(e)
    env = m
    stack = Nil

    while (target.isInstanceOf[Eval] || !stack.isEmpty) {
      eval
    }
    target match {
      case Return(v) => v
      case Throw(s)  => ExceptionValue(s)
      case Eval(e)   => throw new Exception("returning with evaluation still to be done?")
    }
  }

  def eval : Unit = target match {
    case Eval(e) => e match {
      case Var(x) => target = Return(getBinding(x))
      case Z      => target = Return(ZVal)
      case S(n) => {
        target = Eval(n)
        pushExprStack(StackS)
      }
      case Lam(v, t, e) => target = Return(LamVal(v, e, flattenEnv))
      case App(e1, e2) => {
        target = Eval(e1)
        pushExprStack(StackLam(e2))
      }
      case Fix(v, Lam(x, t2, e)) => {
        env = Map(v -> RecursiveLamVal(v, x, e, flattenEnv)) :: env
        target = Eval(Lam(x, t2, e))
        pushExprStack(PopFrame)
      }
      case Fix(v, e) => target = Eval(e) //this will explode on CAFs (eg, recursive non-functions) so don't write them
      case Triv      => target = Return(TrivVal)
      case PairEx(e1, e2) => {
        target = Eval(e1)
        pushExprStack(StackLPair(e2))
      }
      case InL(e) => {
        target = Eval(e)
        pushExprStack(StackInL)
      }
      case InR(e) => {
        target = Eval(e)
        pushExprStack(StackInR)
      }
      case Match(e, rs) => {
        target = Eval(e)
        pushExprStack(StackCase(rs))
      }
      case Fold(mu, t, e) => {
        target = Eval(e)
        pushExprStack(StackFold)
      }
      case Unfold(e) => {
        target = Eval(e)
        pushExprStack(StackUnfold)
      }
      case TypeLam(t, e) => target = Eval(e) //Ignore types
      case TypeApp(e, t) => target = Eval(e) //Ignore types
      case ThrowEx(s)    => target = Throw(s)
      case TryCatch(e1, e2) => {
        target = Eval(e1)
        pushExprStack(StackHandler(e2))
      }
      case CommandExp(c) => target = Return(Action(c, flattenEnv))
    }
    case Return(v) => popExprStack match {
      case StackS => target = Return(SVal(v))
      case StackLam(e2) => {
        target = Eval(e2)
        pushExprStack(StackArg(v))
      }
      case StackArg(LamVal(x, e, clos)) => {
        env = clos + (x -> v) :: env
        target = Eval(e)
        pushExprStack(PopFrame)
      }
      case StackArg(v1) => throw new Exception("Application of a non-function : " + v1) //Typechecker should have caught this
      case StackLPair(e2) => {
        target = Eval(e2)
        pushExprStack(StackRPair(v))
      }
      case StackRPair(v1) => target = Return(PairVal(v1, v))
      case StackInL       => target = Return(InLVal(v))
      case StackInR       => target = Return(InRVal(v))
      case StackCase(Nil) => throw new Exception("Empty set of rules?")
      case StackCase(Rule(p, b) :: rs) => {
        val (e, bind) = runPattern(v, p, b, rs)
        env = bind :: env
        target = Eval(e)
        pushExprStack(PopFrame)
      }
      case StackFold => target = Return(FoldVal(v))
      case StackUnfold => v match {
        case FoldVal(v) => target = Return(v)
        case v          => throw new Exception("Attempt to unfold a non-recursive value " + v) //typechecker should catch
      }
      case StackHandler(e2) => () //if a value is returned, skip the handler
      case PopFrame         => env = env.tail //'tail' should be safe, pops are added only with a frame
    }
    case Throw(e) => popExprStack match {
      case StackHandler(e2) => target = Eval(e2)
      case _                => () //if an exception is being thrown, pop stack
    }
  }

  /*
   * Command
   */

  sealed abstract class CommandTarget
  case class Execute(c : Command) extends CommandTarget
  case class CommandReturn(v : Value) extends CommandTarget

  def executeCommand(c : Command, envv : List[Map[String, Value]]) : Value =
    executeCommand(Execute(c), Nil, envv, Nil)._1

  //we can safely use the same env variable as Exprs do because Expr evaluation always pushes and pops in sync

  def executeCommand(c : CommandTarget, mem : List[Map[String, Value]],
                     envv : List[Map[String, Value]], stk : List[CmdStack]) : (Value, List[Map[String, Value]]) = c match {
    case Execute(c) => c match {
      case Ret(e) => (runEval(e, envv), mem)
      case Bind(x, e, m) => {
        val v = runEval(e, envv)
        v match {
          case Action(m2, closure) => {
            val (v2, mem2) = executeCommand(Execute(m2), mem, closure :: envv, stk) //TODO
            executeCommand(Execute(m), mem2, Map(x -> v2) :: envv, stk) //TODO
          }
          case _ => throw new Exception("Attempt to bind a non-action " + v)
        }
      }
      case Get(x)          => (innerGetBinding(mem, x), mem) //TODO use something other than innerGetBinding //Guarenteed to be there by the typechecker
      case SetCmd(x, e, m) => executeCommand(Execute(m), updateMemory(x, runEval(e, envv), mem), envv, stk)
      case Decl(x, e, m)   => executeCommand(Execute(m), Map(x -> runEval(e, envv)) :: mem, envv, PopBlock :: stk)
    }
    case CommandReturn(v) => stk match {
      case Nil                     => (v, mem)
      //Safe to pull out tail because the only change to mem's blocks-discipline is pushing along with a pop command
      case PopBlock :: s           => executeCommand(CommandReturn(v), mem.tail, envv, s)
      case CmdStackBind(x, m) :: s => executeCommand(Execute(m), mem, Map(x -> v) :: envv, s)
    }
  }

  //Update the outermost stack-bound x
  def updateMemory(x : String, v : Value, mem : List[Map[String, Value]]) : List[Map[String, Value]] = mem match {
    case Nil                     => throw new Exception("Unbound identifier : " + x) //Typechecker should blow up on this first
    case m :: e if m.contains(x) => m + (x -> v) :: e
    case m :: e                  => m :: updateMemory(x, v, e)
  }

  /*
   * Pattern
   */

  sealed abstract class MatchingTarget
  case class Against(p : Pattern, v : Value) extends MatchingTarget
  case class Binding(b : Map[String, Value]) extends MatchingTarget

  var rules : List[Rule] = null //Rules as yet untried
  var matchVal : Value = null //Value being matched against
  var body : Expr = null //The body to be evaluated if the match succeeds
  var patternStack : List[PatStack] = null //The parts of the pattern still unmatched
  var matchingTarget : MatchingTarget = null //Either a pattern against a variable, or a binding being returned

  def runPattern(v : Value, p : Pattern, b : Expr, rs : List[model.Rule]) : (Expr, Map[String, Value]) = {
    rules = rs
    matchVal = v
    body = b
    patternStack = Nil
    matchingTarget = Against(p, matchVal)

    while (!(matchingTarget.isInstanceOf[Binding] && patternStack.isEmpty)) {
      matchPattern
    }
    (body, matchingTarget.asInstanceOf[Binding].b)
  }

  private def matchPattern : Unit = matchingTarget match {
    case Against(WildPat, _)           => matchingTarget = Binding(Map())
    case Against(VarPat(x), v)         => matchingTarget = Binding(Map(x -> v))
    case Against(ZPat, ZVal)           => matchingTarget = Binding(Map())
    case Against(SPat(p), SVal(v))     => matchingTarget = Against(p, v)
    case Against(TrivPat, TrivVal)     => matchingTarget = Binding(Map())
    case Against(InLPat(p), InLVal(v)) => matchingTarget = Against(p, v)
    case Against(InRPat(p), InRVal(v)) => matchingTarget = Against(p, v)
    case Against(PairPat(p1, p2), PairVal(v1, v2)) => {
      patternStack = PatStackLPair(v2, p2) :: patternStack
      matchingTarget = Against(p1, v1)
    }
    case Against(_, _) => rules match { //Match failed; move on to the next pattern
      case Nil => throw new Exception("No pattern match found for " + matchVal)
      case Rule(p, b) :: rs => {
        rules = rs
        body = b
        patternStack = Nil
        matchingTarget = Against(p, matchVal)
      }
    }
    case Binding(bind) => patternStack match {
      case Nil => throw new Exception("Should have aborted the pattern-match driver loop!") //This is the escape case
      case PatStackLPair(v2, p2) :: ps => {
        patternStack = PatStackRPair(bind) :: ps
        matchingTarget = Against(p2, v2)
      }
      case PatStackRPair(m1) :: ps if ((m1.keySet & bind.keySet).isEmpty) => {
        patternStack = ps
        matchingTarget = Binding(m1 ++ bind)
      }
      case PatStackRPair(m1) :: ps => throw new Exception("Patterns cannot have repeated variables") //genuine error; as of now, no way to check
    }
  }

  /*
   * Defn/Prog
   */

  def evalDefn(m : Map[String, Value], d : Defn) : Map[String, Value] = d match {
    case ExprDefn(n, b, args) => m + (n -> runEval(b, List(m)))
    case TypeDefn(n, t)       => m
  }

  def evaluate(p : Prog) : Value = executeCommand(p.e, List(p.defs.foldLeft(Map[String, Value]())(evalDefn)))

}