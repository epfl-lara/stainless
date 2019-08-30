import stainless.annotation._

object TypeMembers2 {
  abstract class M {
    @mutable
    type T
    def c(t: T): Unit
  }

  case class A(var x: BigInt)

  case class F() extends M {
    type T = A

    def c(t: T) = {
      t.x += 2
    }
  }

  def test(x: F) = {
    val a = A(40)
    x.c(a)
    assert(a.x == 42)
  }
}
