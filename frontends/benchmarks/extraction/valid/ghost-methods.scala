package ghost.methods

import stainless.lang._
import stainless.annotation.ghost

object GhostMethods {

  @ghost
  def ghostMethod1(x: BigInt): BigInt = BigInt(1)

  def ghostMethod2(@ghost x: BigInt, y: BigInt): BigInt = BigInt(1)

  def f(@ghost x: BigInt, p: BigInt): BigInt = BigInt(0)
  def g(y: BigInt) : BigInt = BigInt(0)

  def polyG[A](@ghost g: A, zero: A): A = zero

  def bar: Unit = {
    // assign regular code to ghost vars is allowed
    @ghost var var1: BigInt = BigInt(1)

    // calling ghost method in ghost context is allowed
    @ghost val x: BigInt = ghostMethod1(10)

    // assigning to ghost method can call ghost code
    var1 = ghostMethod1(x)

    // non-ghost method passing real code args
    ghostMethod2(BigInt(10), BigInt(11))

    // only one argument is ghost
    ghostMethod2(x, BigInt(10))

    // Viktor's example (nested real code inside ghost code should be allowed)
    @ghost var z: BigInt = BigInt(0)
    val r: BigInt = f(g(z), 100)

    // poly method has one ghost parameter
    polyG(x, r)
  }
}
