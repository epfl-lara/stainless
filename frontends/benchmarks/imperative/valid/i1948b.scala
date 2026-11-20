import stainless.lang.*

object i1948b:
  case class Box(a: Array[Int])

  def clear(b: Box): Unit =
    if b.a.length > 0 then
      b.a(0) = 0

  def f(arr: Array[Int]): Unit = {
    val b = Box(arr)

    clear(b)
  }.ensuring(_ => arr.length == 0 || arr(0) == 0)
