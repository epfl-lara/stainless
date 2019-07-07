import stainless.lang._
import stainless.annotation._

object ValModification {

  @mutable
  trait T {
    val x: BigInt

    def havoc(): Unit = {
      (??? : Unit)
    } ensuring { res =>
      this.x == old(this).x
    }
  }

  def f(t: T) = {
    val y = t.x
    t.havoc()
    assert(y == t.x)
  }
}
