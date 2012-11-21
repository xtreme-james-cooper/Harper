package model

sealed abstract class Process(name : String) {
  override def toString : String = name
}

case object Stop extends Process("stop")
case class Atomic(m : Command) extends Process("atomic " + m)
case class Parallel(p1 : Process, p2 : Process) extends Process("(" + p1 + "||" + p2 + ")")
case class NewChannel(a : String, t : Type, p : Process) extends Process("new " + a + ":" + t + "." + p)