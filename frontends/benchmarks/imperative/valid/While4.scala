import stainless.lang._
import stainless.math._

import While4._

object While4 {
  val sizeLimit: Int = 1000000
}

case class While4[T](array: Array[T], lessThan: (T, T) => Boolean) {
  require(array.size < sizeLimit)

  def insert(elem: T): Unit = {
    var l: Int = -1
    var h: Int = array.size
    val n: Int = array.size

    (while (l + 1 != h) {
      decreases(max(0, h - l))

      val m = (l + h) >> 1

      if (lessThan(elem, array(m))) {
        h = m
      } else {
        l = m
      }

    }) invariant (-1 <= l && l < h && h <= n && array.size == n)

    var i = n - 1
    (while (i > h) {
      decreases(i)
      array(i) = array(i-1)
      i = i - 1
    }) invariant (0 <= h && h <= i && i <= n-1 && array.size == n)

  }
}
