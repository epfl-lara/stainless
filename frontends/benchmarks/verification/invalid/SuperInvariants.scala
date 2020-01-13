
object SuperInvariants {

  sealed abstract class Foo {
    require(x != 0)
    val x: BigInt
  }

  case class Bar(x: BigInt) extends Foo {
    require(x != 1)
  }

  def bad0: Foo = Bar(0) // invalid
  def bad1: Foo = Bar(1) // invalid
  def ok2: Foo  = Bar(2) // valid

}
