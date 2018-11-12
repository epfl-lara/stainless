
import stainless.lang._
import stainless.annotation._

object AnyMut {

  case class Mut(var v: BigInt)

  @extern
  def doNothing(@pure x: Any): Unit = ()

  @extern
  def doSomething(x: Any): Unit = ()

  def testNothing = {
    val m = Mut(0)
    doNothing(m)
    assert(m.v != 0) // invalid
  }

  def testSomething = {
    val m = Mut(0)
    doSomething(m)
    assert(m.v == 0) // invalid
    assert(m.v != 0) // invalid
  }

}
