import stainless.lang._

case class Inner(var int: Int)
case class Outer(var inner: Inner)

// The mutable object is a parameter: a field of the trait may not refer to a mutable object
// (see extraction/invalid/FreshCopyTraitField).
trait FreshCopy {
  def f(o: Outer) = {
    require(o.inner.int == 123)

    val fresh = freshCopy(o)
    o.inner.int  = 456
    assert(fresh.inner.int == 123)
    assert(o.inner.int == 456)

    val fresh2 = freshCopy(o)
    o.inner = Inner(789)
    assert(fresh.inner.int == 123)
    assert(fresh2.inner.int == 456)
    assert(o.inner.int == 789)
  }
}
