/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._

object Fibonacci {
  def fib(x: BigInt) : BigInt = {
    require(x >= 0)
    decreases(x)
    if(x < 2) {
      x
    } else {
      fib(x - 1) + fib(x - 2)
    }
  }

  def check() : Boolean = {
    fib(5) == BigInt(5)
  } ensuring(_ == true)
}
