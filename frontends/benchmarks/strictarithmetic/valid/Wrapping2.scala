import stainless.math._

object Wrapping2 {

  def double(x: Int, y: Int) = wrapping {
    x + y - (x * 2 - y * 10) // OK
  }

}
