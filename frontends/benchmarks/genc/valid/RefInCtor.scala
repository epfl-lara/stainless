import stainless._
import stainless.annotation._

object RefInCtor {

  case class Ref[T](var x: T)

  case class Container[T](ref: Ref[T])

  @cCode.`export`
  def test1(v: Int): Unit = {
    val cont = Container(Ref(v))
    // The above is fine, but the following is not (see invalid/InvalidReference1)
    // val rf = Ref(v)
    // val cont = Container(rf)
  }

  @cCode.`export`
  def test2(v: Int): Unit = {
    val cont = Container({val tmp = Ref(v); tmp}) // tmp is a ref. to a mutable variable, but is local to its block.
  }

  @cCode.`export`
  def main(): Unit = ()
}
