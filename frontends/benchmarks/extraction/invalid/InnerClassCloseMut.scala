
object InnerClassCloseMut {

  def test: Int = {
    var x: Int = 1

    case class Wrong() {
      def foo = {
        x = x + 1
        x
      }
    }

    Wrong().foo
  }
}
