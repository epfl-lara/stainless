import stainless.math._
import stainless.annotation._

object Wrapping2 {

  def double1(x: Int, y: Int) = wrapping {
    x + y - (x * 2 - y * 10) // OK
  }

  @wrapping
  def double2(x: Int, y: Int) = {
    x + y - (x * 2 - y * 10) // OK
  }

}
