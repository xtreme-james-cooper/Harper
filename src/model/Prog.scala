package model

class Prog(val defs : List[Defn], val e : Expr) {
  override def toString : String = defs.foldLeft("")({case (s, defn) => s + defn}) + e
}