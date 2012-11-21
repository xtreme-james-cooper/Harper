package typechecker

import model.{ Unknown, Type }

object TypeChecker {

  //not necessarily a var; done this way to save the effort of piping it around
  var typeVarCounter : Int = 0

}

class TypeChecker {

  type Constraint = (Type, Type)
  type Env = Map[String, Type]

  def baseEnv : (Env, Env) = (Map(), Map())

  def newUnknown : Type = {
    TypeChecker.typeVarCounter = TypeChecker.typeVarCounter + 1
    Unknown(TypeChecker.typeVarCounter)
  }

  def verifyConstraints(t : Type, cs : List[Constraint]) : Type = cs.flatMap({ case (t1, t2) => t1 ~=~ t2 }) match {
    case Nil                           => t
    case (Unknown(i), b) :: cs         => verifyConstraints(t.swap(i, b), cs.map({ case (x, y) => (x.swap(i, b), y.swap(i, b)) }))
    case (a, Unknown(i)) :: cs         => verifyConstraints(t.swap(i, a), cs.map({ case (x, y) => (x.swap(i, a), y.swap(i, a)) }))
    case (t1, t2) :: cs if !(t1 == t2) => throw new Exception("Constraint failure: " + t1 + " != " + t2)
    case (t1, t2) :: cs                => verifyConstraints(t, cs)
  }

  //Replace unknowns that we have information about
  def updateConstraint(unkId : Int, t2 : Type)(cs : List[Constraint]) : List[Constraint] =
    cs.map({ case (a, b) => (a.swap(unkId, t2), b.swap(unkId, t2)) })

}