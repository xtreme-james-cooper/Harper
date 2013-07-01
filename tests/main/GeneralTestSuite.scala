package main

import org.junit.Assert._
import org.junit.Test

class GeneralTestSuite {

  def assertThrows[A](e : Exception, t : => A) : Unit = {
    try {
      t
      fail
    } catch {
      case ex : Exception => assertEquals(ex, e)
    }

  }

}