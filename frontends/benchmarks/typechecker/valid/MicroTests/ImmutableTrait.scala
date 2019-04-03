trait ImmutableTrait

trait B {
  def f(a: ImmutableTrait): Unit

  def g(a: ImmutableTrait): Unit = {
    val a0 = a
    f(a)
    // We can ensure that `a` has not changed during the call to `f`
    // because ImmutableTrait has no var's and is assumed immutable.
    // See similar example in imperative/invalid/MutableTrait.scala
    assert(a == a0)
  }
}
