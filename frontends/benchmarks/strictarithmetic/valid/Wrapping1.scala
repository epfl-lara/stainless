import stainless.math._
import stainless.annotation._

object Wrapping1 {

  def double1(x: Int) = wrapping {
    x + x // OK
  }

  @wrapping
  def double2(x: Int) = {
    x + x // OK
  }

}
