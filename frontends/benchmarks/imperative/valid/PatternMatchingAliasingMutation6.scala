/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._

object PatternMatchingAliasingMutation6 {

  case class Wrapper(var x: Int)

  def foo(): Int = {
    var c = 1

    def get0(): Int = {
      c -= 1
      0
    }

    val array = Array(Wrapper(42))
    array(get0()) match {
      case w if w.x == 42 => w.x = 0
      case w => w.x = -1
    }

    array(0).x + c
  } ensuring { _ == 0 }

}

