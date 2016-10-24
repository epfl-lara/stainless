/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object AndTest {

   def nonterm(x: BigInt) : BigInt = {
     nonterm(x + 1)
   } ensuring(res => false)

   def precond(y : BigInt) = y < 0

   /**
    * Leon should find a counter-example here.
   **/
   def foo(y: BigInt) : Boolean = {
     require(precond(y))
     y >= 0 && (nonterm(0) == 0)
   } holds
}
