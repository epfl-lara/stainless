/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object AndTest {

   def nonterm(x: BigInt) : BigInt = {
     nonterm(x + 1)
   }.ensuring(res => false)

   def precond(y : BigInt) = y < 0

   /**
    * Stainless should find a counter-example here.
   **/
   def foo(y: BigInt) : Boolean = {
     require(precond(y))
     y >= 0 && (nonterm(0) == 0)
   }.holds
}
