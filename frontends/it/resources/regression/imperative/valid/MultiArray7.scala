import stainless.lang._

object MultiArray7 {

  def test: Int = {

    val a: Array[Array[Int]] = Array.fill(10)(Array.fill(10)(0))

    var i = 0
    (while(i < 10) {
      a(i) = Array.fill(10)(i)
      i += 1
    }) invariant( a.length == 10 && a(3).length == 10 && i >= 0 && i <= 10 && ((i >= 4) ==> (a(3)(3) == 3)) )
    a(3)(3)
  } ensuring(_ == 3)

}
