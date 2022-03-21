import stainless.lang._
import stainless.annotation._

// FIXME: Used to be accepted and verified (now rejected at extraction)
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
    // "Unsupported val definition (couldn't compute targets and there are mutable variables shared between the binding and the body)"
    // This test case used to be accepted because a special case was triggered in AntiAliasing due to `target` not being referenced
    // in the body of the block.
    // Now, the Normalizer introduces a binding `targetBound` for the call to `get_mut` and that special case is no longer triggered
    // because `targetBound` and `target` are alive after the call to `get_mut`.
    get_mut[Int](target) match {
      case Some(v) => v.value = 456
      case _       => error[Nothing]("no value")
    }
    assert(
      target.value == Container(MutCell[Option[Int]](Some(MutCell(456))))
    )
  }
}
