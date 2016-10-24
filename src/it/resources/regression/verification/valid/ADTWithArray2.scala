import leon.collection._

object ADTWithArray2 {

  case class A1(x: Int)

  case class B(t: Array[A1])

  def test(b: B): Int = {
    require(b.t.length > 2)
    b.t.length
  } ensuring(a => a > 0)

}
