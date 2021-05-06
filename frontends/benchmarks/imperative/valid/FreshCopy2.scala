import stainless.lang._
import stainless.annotation._

case class Container[@mutable T](var t: T)

trait FreshCopy2 {
  def f() = {
    var c = Container(Container(Container(123)))

    val fresh = freshCopy(c)
    c.t = Container(Container(456))
    assert(fresh.t.t.t == 123)

    var fresh2 = freshCopy(c.t.t)
    c.t.t.t = 789
    assert(fresh.t.t.t == 123)
    assert(fresh2.t == 456)
    assert(c.t.t.t == 789)

    var fresh3 = freshCopy(fresh2)
    fresh2.t = -111
    assert(fresh.t.t.t == 123)
    assert(fresh2.t == -111)
    assert(fresh3.t == 456)

    fresh3 = Container(-222)
    assert(fresh.t.t.t == 123)
    assert(fresh2.t == -111)
    assert(fresh3.t == -222)
  }
}
