/* Copyright 2009-2016 EPFL, Lausanne */

object Fibonacci {
  def fib(x: BigInt) : BigInt = {
    require(x >= 0)
    if(x < 2) {
      x
    } else {
      fib(x - 1) + fib(x - 2)
    }
  }

  // requires that fib is universally quantified to work...
  def check() : Boolean = {
    fib(5) == BigInt(5)
  } ensuring(_ == true)
}
