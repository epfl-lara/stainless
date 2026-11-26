import stainless.lang._

case class Inner(var int: Int)
case class Outer(var inner: Inner)

// This used to be imperative/valid/FreshCopy. It is rejected because the field `o` of the trait
// refers to a mutable object, as for the fields of concrete classes and of objects.
//
// A field that is not a constructor parameter is a function that evaluates its initialiser: each
// `o` is a fresh `Outer(Inner(123))`, hence the mutations of `o` below would be lost. Stainless
// used to accept them here, by mistake. With `case class C() extends FreshCopy`, it then proved
// that `c.o.inner.int == 123` holds after `c.o.inner.int = 456`, whereas it is 456 in Scala.
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
