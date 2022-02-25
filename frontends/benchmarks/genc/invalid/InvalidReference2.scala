import stainless._
import stainless.annotation._

object InvalidReference2 {
  case class Ref[T](var x: T)
  case class Container[T](ref: Ref[T])

  @cCode.`export`
  def test1(v: Int): Unit = {
    val rf = Ref(v)
    // Invalid reference: cannot construct an object from a mutable variable.
    val cont = Container({val dummy = 3; rf})
  }
}
