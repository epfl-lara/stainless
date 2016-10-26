/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.annotation._
import stainless.lang._

object BigArray {

  def big(a: Array[Int]): Int = {
    require(a.length >= 10 && a(7) == 42)
    a.length
  } ensuring(_ <= 1000000000)

}
