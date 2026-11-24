import stainless._
import stainless.lang._
import stainless.annotation._
import stainless.io.StdOut

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

  // A missing implementation must be unreachable
  def bar: Nothing = {
    require(false)
    ???
  }

  def foo[T](t: T, arg: Int): T = {
    require(arg > 0)
    if (arg == 0) {
      def boom: Nothing = {
        // This will capture `arg` and `boom` will get the PC arg > 0 && arg == 0 (i.e. false)
        val pullingArgIntoThePit = arg
        error[Nothing]("boom indeed")
      }
      boom
    }
    else if (arg < 0) bar
    else t
  }
}

