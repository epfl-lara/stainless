import stainless.lang.*

object i1948c:
  case class Box(a: Array[Int])

  def set(b: Box, i: Int): Unit =
    require(0 <= i && i < b.a.length)
    b.a(i) = 0

  /** False when `i == j` and `arr(i)` was not 0. */
  def f(arr: Array[Int], i: Int, j: Int): Unit = {
    require(0 <= i && i < arr.length)
    require(0 <= j && j < arr.length)

    val b = Box(arr)

    set(b, i)
  }.ensuring(_ => arr(j) == old(arr)(j))
