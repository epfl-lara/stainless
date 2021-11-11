import stainless.math._
import stainless.annotation.{wrapping => wrappingAnnot}

object Wrapping2 {

  def double1(x: Int, y: Int) = wrapping {
    x + y - (x * 2 - y * 10) // OK
  }

  @wrappingAnnot
  def double2(x: Int, y: Int) = {
    x + y - (x * 2 - y * 10) // OK
  }

}
