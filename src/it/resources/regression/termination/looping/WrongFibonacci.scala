/* Copyright 2009-2016 EPFL, Lausanne */


object Test {
  
  def looping_fib(n: BigInt): BigInt = {
    looping_fib(n-1) + looping_fib(n-2)
  } ensuring {res => res == (5*n + 1)*(5*n - 1)}
  
}
