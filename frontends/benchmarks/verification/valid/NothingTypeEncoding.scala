import stainless._
import stainless.lang._

object NothingTypeEncoding {
  sealed abstract class List[T]
  case class Nil[T]() extends List[T]
  case class Cons[T](head: T, tail: List[T]) extends List[T]

  // This should work as expected
  def first[T](self: List[T]): T = {
    require(self match {
      case Nil() => false
      case _ => true
    })
    self match {
      case Cons(v, _) => v
      case _ => error[Nothing]("Empty list")
    }
  }

  /* Commented out because this will fail (not crash) verification.
  def bar: Nothing = ???
  // This is transformed to: error[T]
  def foo[T]: T = bar
   */
}

