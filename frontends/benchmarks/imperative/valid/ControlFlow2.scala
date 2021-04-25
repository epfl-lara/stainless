import stainless.lang._

object ControlFlow2 {

  def foo(x: Option[BigInt], a: Boolean, b: Boolean): BigInt = {
    if (a && b) {
      return 1
    }

    val y = x match {
      case None()       => return 0
      case Some(x) if a => return x + 1
      case Some(x) if b => return x + 2
      case Some(x)      => x
    };

    -y
  }

  def testFoo: Unit = {
    assert(foo(None(), false, false) == 0)
    assert(foo(Some(10), true, true) == 1)
    assert(foo(Some(10), true, false) == 11)
    assert(foo(Some(10), false, true) == 12)
    assert(foo(Some(10), false, false) == -10)
  }

}
