import stainless.lang._
import stainless.annotation._

trait MutableTrait {
  var x: BigInt
}

trait B {
  def f(a: MutableTrait): Unit

  def g(a: MutableTrait): Unit = {
    @ghost val a0 = snapshot(a)
    f(a)
    // we cannot ensure that `a` has not changed during the call to `f`
    // See similar example in verification/valid/ImmutableTrait.scala
    stainless.lang.StaticChecks.assert(a == a0)
  }
}
