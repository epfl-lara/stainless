import stainless.annotation.*

/** GenC does not support arrays of functions. */
object ArrayOfFunctions:

  def inc(x: Int): Int = x + 1

  @cCode.`export`
  def main(): Unit =
    val fs: Array[Int => Int] = Array[Int => Int]((x: Int) => inc(x))
    val r: Int = fs(0)(1)
    ()
