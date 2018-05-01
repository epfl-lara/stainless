import stainless.lang._

object ADTInvariantCheck {

  case class Foo(x: BigInt) {
    require(x != 0)
  }

  def fooFailed1(x: BigInt) = Foo(x)
  def fooFailed2 = Foo(0)
  def fooFailed3(x: BigInt) = {
    require(x <= 0)
    if (x < 10) Foo(x) else Foo(x - 10)
  }

  def fooOk1 = Foo(1)
  def fooOk2(x: BigInt) = {
    require(x > 0)
    Foo(x)
  }

  case class Bar(arg1: BigInt, arg2: Option[BigInt]) {
    require(arg1 > 0 || arg2.isDefined)
  }

  def barFailed1: Bar = Bar(-1, None())

  def barOk1: Bar = Bar(-1, Some(1))
  def barOk2: Bar = Bar(12, None())

}

