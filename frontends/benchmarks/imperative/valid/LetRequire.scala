import stainless.annotation._

object LetRequire {

  case class C(var x: BigInt)

  def increment(c: C): Unit = {
    val d = c.x + 1
    require(d <= 100)

    c.x += 1
  }

  def test() = {
    increment(C(99))
  }

}
