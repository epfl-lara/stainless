import leon.collection._

object ADTWithArray1 {

  case class A1(x: Int)

  case class B(t: Array[A1])

  def test(b: B): A1 = {
    require(b.t.length > 0 && b.t(0).x > 0)
    b.t(0)
  } ensuring(a => a.x >= 0)

}
