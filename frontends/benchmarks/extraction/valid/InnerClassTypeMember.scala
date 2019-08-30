
object InnerClassTypeMember {

  abstract class Foo {
    type Bar
    def baz(b: BigInt): Bar
  }

  def foo: Foo = {
    case class LocalFoo() extends Foo {
      type Bar = BigInt
      def baz(b: BigInt): Bar = b + 41
    }
    LocalFoo()
  }

}
