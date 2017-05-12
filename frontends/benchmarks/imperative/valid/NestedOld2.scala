/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object NestedOld2 {

  def test(): Int = {
    var counterPrev = 0
    var counterNext = 1

    def step(): Unit = {
      require(counterNext == counterPrev + 1)
      counterPrev = counterNext
      counterNext = counterNext+1
    } ensuring(_ => {
      counterPrev == old(counterNext) && 
      counterNext == old(counterNext) + 1 &&
      counterPrev == old(counterPrev) + 1
    })

    step()
    step()
    counterNext
  } ensuring(_ == 3)

}
