
object CopyInv {

  case class Foo(x: BigInt) {
    require(x > 0)
  }

  def prop(foo: Foo, y: BigInt) = {
    require(y > 1)
    foo.copy(x = y)
  }

}
