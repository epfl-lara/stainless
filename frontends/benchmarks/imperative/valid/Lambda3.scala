import stainless.annotation._

object Lambda3 {
  def app[@mutable A](mkA: A, ping: A => Unit, get: A => BigInt): BigInt = {
    val f: A => BigInt = ((a: A) => {ping(a); get(a)+1})
    f(mkA)
  } ensuring(res => true)

  case class Cell[T](var content: T)

  def test = {
    val c = Cell[BigInt](42)
    val myPing = {
      (c1 : Cell[BigInt]) => c1.content = c1.content + 100
    }
    val res: BigInt = app[Cell[BigInt]](c, myPing, _.content)
    assert(c.content == 142)
    assert(res == 143)
  }
}
