/* Copyright 2009-2016 EPFL, Lausanne */

object NestedFunState2 {

  def countConst(): Int = {

    var counter = 0

    def inc(): Unit = {
      counter += 1
    }

    inc()
    inc()
    inc()
    counter
  } ensuring(_ == 3)

}
