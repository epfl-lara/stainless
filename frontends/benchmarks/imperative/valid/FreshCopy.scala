import stainless.lang._

case class Inner(var int: Int)
case class Outer(var inner: Inner)

trait FreshCopy {
  val o: Outer = Outer(Inner(123))

  def f() = {
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
