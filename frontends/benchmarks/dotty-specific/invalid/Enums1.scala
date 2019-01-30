
import stainless.lang._

object Enums1 {

  enum Color {
    case Red, Green, Blue
  }

  def test(c: Color) = {
    assert(c == Color.Red || c == Color.Green || c == Color.Blue)
  }

}
