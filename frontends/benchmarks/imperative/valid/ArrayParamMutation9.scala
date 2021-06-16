import stainless.lang._

object ArrayParamMutation9 {
  def abs(a: Array[Int]): Unit = {
    require(a.length > 0)
    var i = 0;
    (while (i < a.length) {
      a(i) = if (a(i) < 0) -a(i) else a(i)
      i = i + 1
    }) invariant(i >= 0)
  }


  def main = {
    val a = Array(0, -1, 2, -3)

    abs(a)

    a(0) + a(1) - 1 + a(2) - 2 + a(3) - 3 // == 0
  }

}
