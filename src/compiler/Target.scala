package compiler

import model.{ Value, Expr }

sealed abstract class Target
case class Eval(e : Expr) extends Target
case class Return(v : Value) extends Target
case class Throw(s : String) extends Target
