import stainless.math._
import stainless.annotation._

object Wrapping2 {

  @wrapping
  def foo1(x: Int, y: Int) = {
    x << y // Still invalid
  }

}
