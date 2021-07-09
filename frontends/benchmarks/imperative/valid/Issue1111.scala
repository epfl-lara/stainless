import stainless.annotation._

object Issue1111 {
  sealed abstract class Option[@mutable T]
  case class None[@mutable T]()               extends Option[T]
  case class Some[@mutable T](_0: MutCell[T]) extends Option[T]

  sealed case class Tuple2[@mutable T0, @mutable T1](_0: MutCell[T0], _1: MutCell[T1])

  case class MutCell[@mutable T](var value: T)

  def get_mut[@mutable V](self: MutCell[Tuple2[String, V]], key: String): Option[V] =
    if (self.value._0.value == key) Some[V](self.value._1)
    else None[V]()

  @pure
  def main: Unit = {
    val target = MutCell[Tuple2[String, Int]](
      Tuple2[String, Int](MutCell[String]("bar"), MutCell[Int](0))
    )
    get_mut[Int](target, "foo") match {
      case Some(v1) =>
        v1.value = 123 // if this line is commented, all passes
      case _ =>
        ()
    }
  }
}
