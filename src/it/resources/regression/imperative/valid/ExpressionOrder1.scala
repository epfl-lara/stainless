/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object ExpressionOrder1 {

  def test1 = {
    var x = 0

    def bar(y: Int) = {
      def fun(z: Int) = 1 * x * (y + z)

      fun(3)
    }

    bar(2) == 0
  }.holds

}
