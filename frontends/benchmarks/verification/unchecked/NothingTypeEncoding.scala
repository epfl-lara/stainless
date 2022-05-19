import stainless._
import stainless.lang._
import stainless.annotation._
import stainless.io.StdOut

// Should be accepted, but is rejected
// (see verification/valid/NothingTypeEncoding for a variant that verifies)
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

  def bar: Nothing = ???

  def foo[T](t: T, arg: Int): T = {
    require(arg > 0)
    if (arg == 0) {
      // `boom` does not know that arg == 0 is false because it does not capture it.
      def boom: Nothing = error[Nothing]("boom indeed")
      boom
    }
    else if (arg < 0) bar
    else t
  }
}

