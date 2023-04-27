import scala.collection.mutable.StringBuilder

object i827b {
  def test: Char = {
    val s: String = "abc"
    s(0)
  }

  def test2(x: StringBuilder): Unit = {
    x += 'a'
  }

  def test3(y: StringBuilder): Unit = {
    y += 'b'
  }
}