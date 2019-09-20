import stainless.math._

object Wrapping1 {

  def double(x: Int) = wrapping {
    x + x // OK
  }

}
