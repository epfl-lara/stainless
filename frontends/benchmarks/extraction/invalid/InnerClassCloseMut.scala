
object InnerClassCloseMut {

  abstract class Test {
    def foo: Int
  }

  def test: Int = {
    var x: Int = 1

    case class Wrong() extends Test {
      def foo = {
        x = x + 1
        x
      }
    }

    Wrong().foo
  }
}
