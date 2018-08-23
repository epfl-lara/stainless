
object CopyInv {

  case class Foo(x: BigInt) {
    require(x > 0)
  }

  def prop(foo: Foo, y: BigInt) = {
    foo.copy(x = y)
  }

}
