package compiler

sealed abstract class State(val isTermination : Boolean)
case object EvalExpr extends State(false)
case object Return extends State(true)
case object Throw extends State(true)
case object EvalRules extends State(false)
case object EvalMatch extends State(false)
