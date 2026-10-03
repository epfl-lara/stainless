package erased.methods

import stainless.lang._
import stainless.annotation.ghost

object ErasedMethods {

  @ghost def erasedMethod1(x: BigInt): BigInt = BigInt(1)

  def erasedMethod2(erased x: BigInt, y: BigInt): BigInt = BigInt(1)

  def f(erased x: BigInt, p: BigInt): BigInt = BigInt(0)
  def g(y: BigInt) : BigInt = BigInt(0)

  def polyG[A](erased g: A, zero: A): A = zero

  def bar: Unit = {
    // assign regular code to erased vars is allowed
    erased var var1: BigInt = BigInt(1)

    // calling erased method in erased context is allowed
    erased val x: BigInt = erasedMethod1(10)

    // assigning to erased method can call erased code
    var1 = erasedMethod1(x)

    // non-erased method passing real code args
    erasedMethod2(BigInt(10), BigInt(11))

    // only one argument is erased
    erasedMethod2(x, BigInt(10))

    // nested real code inside erased code should be allowed
    erased var z: BigInt = BigInt(0)
    val r: BigInt = f(g(z), 100)

    // poly method has one erased parameter
    polyG(x, r)
  }
}
