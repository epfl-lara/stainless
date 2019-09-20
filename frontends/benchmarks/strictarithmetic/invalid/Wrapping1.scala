import stainless.math._

object Wrapping1 {

  def foo1(x: Int, y: Int) = wrapping {
    x << y // Still invalid
  }

}
