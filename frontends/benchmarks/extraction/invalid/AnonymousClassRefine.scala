
import stainless.lang._

object AnonymousClassesRefine {

  abstract class Foo {
    def bar: Int
  }

  def stuff: Boolean = {
    val foo = new Foo {
      def bar: Int = 1
      val baz: Boolean = true
    }

    foo.baz
  }.holds

}
