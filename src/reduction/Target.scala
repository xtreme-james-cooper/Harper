package reduction

sealed abstract class Target[E, V]
case class Eval[E, V](e : E) extends Target[E, V]
case class Return[E, V](v : V) extends Target[E, V]
case class Throw[E, V](s : String) extends Target[E, V]
