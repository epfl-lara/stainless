import stainless.lang._
import stainless.annotation._

object ExternFallback2 {

  sealed trait Test {
    def something: BigInt
  }

  @ignore
  case class ANewHope(x: BigInt) extends Test {
    def something = x
  }

  case class TheForceAwakens(y: BigInt) extends Test {
    def something = y
  }

  @extern
  def aNewHope(x: BigInt): ANewHope = ANewHope(x)

  val foo: Test = aNewHope(42)

  def test1 = assert(foo == foo)                                     // valid
  def test2 = assert(foo.something == 42)                            // invalid
  def test3 = assert(foo.something != 42)                            // invalid
  def test4 = assert(foo == TheForceAwakens(42))                     // invalid
  def test5 = assert(foo != TheForceAwakens(42))                     // invalid
  def test6 = assert(foo.something == TheForceAwakens(42).something) // invalid

}
