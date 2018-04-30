
object hello {

  abstract class Foo {
    require(foo != 0)
    def foo: BigInt
  }

  case class Hello() extends Foo {
    def foo = 0
  }

  case object invalid extends Foo {
    def foo = 0
  }

  case object valid extends Foo {
    def foo = 42
  }

  def testMethodAccess = {
    valid.foo
  }

}
