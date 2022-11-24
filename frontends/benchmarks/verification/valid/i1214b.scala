import stainless.lang._

object i1214b {
  abstract sealed class Ordinal
  case class Nat() extends Ordinal
  case class Transfinite(in: Ordinal) extends Ordinal //removing Ordinal removes location information

  def free(c: Transfinite): Unit = {
    assert(c.isInstanceOf[Transfinite])
  }

  def bar(): Unit = {
    def inner(c: Transfinite): Unit = {
      assert(c.isInstanceOf[Transfinite])
    }
  }
}