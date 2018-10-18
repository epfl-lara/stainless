trait MutableTrait {
  var x: BigInt
}

trait B {
  def f(a: MutableTrait): Unit

  def g(a: MutableTrait): Unit = {
    val a0 = a
    f(a)
    // we cannot ensure that `a` has not changed during the call to `f`
    // See similar example in verification/valid/ImmutableTrait.scala
    assert(a == a0)
  }
}
