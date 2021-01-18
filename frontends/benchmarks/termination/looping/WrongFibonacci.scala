/* Copyright 2009-2021 EPFL, Lausanne */


object Fibonacci {
  
  def looping_fib(n: BigInt): BigInt = {
    looping_fib(n-1) + looping_fib(n-2)
  } ensuring {res => res == (5*n + 1)*(5*n - 1)}
  
}
