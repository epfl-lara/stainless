import stainless.lang._
import stainless.annotation._

object Mutable {
  sealed case class MutCell[@mutable T](var value: T)
  sealed case class Container[T](field: MutCell[Option[T]])

  sealed abstract class Option[@mutable T]
  case class None[@mutable T]()               extends Option[T]
  case class Some[@mutable T](_0: MutCell[T]) extends Option[T]

  def get_mut[T](self: MutCell[Container[T]]): Option[T] =
    self.value.field match {
      case MutCell(Some(t)) => Some[T](t)
      case _                => None[T]()
    }

  @pure def main: Unit = {
    val target: MutCell[Container[Int]] = MutCell(
      Container(MutCell(Some(MutCell(123))))
    )
    get_mut[Int](target) match {
      case Some(v) => v.value = 456               // AntiAliasing replaces `v.value = 456` with `()`
      case _       => error[Nothing]("no value")
    }
    assert(
      target.value == Container(MutCell[Option[Int]](Some(MutCell(456))))
    )
  }
}
