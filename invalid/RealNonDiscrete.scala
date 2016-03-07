/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.annotation._

object RealNonDiscrete {

  def nonDiscrete(x: Real): Boolean = {
    require(x > Real(1) && x < Real(3))
    x == Real(2)
  } holds

}
