import stainless.annotation._

object ContainerHOFs {
  case class Container[@mutable T](t: T)
  case class Counter(var v: BigInt)

  def apply1[@mutable T](x: T)(f: T => Unit): Unit = f(x)
  def apply2[@mutable T](x: Container[T])(f: T => Unit): Unit = f(x.t)
  def apply3[@mutable T](x: Container[T])(f: Container[T] => Unit): Unit = f(x)

  def test1() = {
    val cc = Container(Counter(0))
    apply1(cc)(cc => cc.t.v = 1)
    assert(cc.t.v == 1)
  }

  def test2() = {
    val cc = Container(Counter(0))
    apply2(cc)(c => c.v = 1)
    assert(cc.t.v == 1)
  }

  def test3() = {
    val cc = Container(Counter(0))
    apply3(cc)(cc => cc.t.v = 1)
    assert(cc.t.v == 1)
  }
}
