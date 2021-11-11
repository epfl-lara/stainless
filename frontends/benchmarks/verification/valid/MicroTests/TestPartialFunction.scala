/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object TestPartialFunction {

  // This checks that the extraction of partial lambda function is correctly handled.
  def foo(y: BigInt): Boolean = {
    require(y != 0)
    val f = PartialFunction { (x: BigInt) => require(x != 0); (2 * x) / x }
    assert( !f.pre(0) ) // the precondition...
    assert( f.pre(1) )  // ... is not a constant
    f(y) == 2
  }.holds

}

