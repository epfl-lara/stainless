import stainless.math._
import stainless.annotation.{wrapping => wrappingAnnot}

object Wrapping1 {

  def double1(x: Int) = wrapping {
    x + x // OK
  }

  @wrappingAnnot
  def double2(x: Int) = {
    x + x // OK
  }

}
