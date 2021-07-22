import stainless.annotation._
import stainless.lang._

object Issue1111c {

  case class TT(mut: MutCell[Int])
  case class Container[@mutable K, @mutable V](pair: MutCell[Option[TT]])

  sealed abstract class Option[@mutable T]
  case class Some[@mutable T](_0: MutCell[T]) extends Option[T]
  case class None[@mutable T]() extends Option[T]

  case class MutCell[@mutable T](var value: T)

  case class Data(_0: MutCell[String])

  def p[@mutable K](key: K): Boolean = true

  def get_mut(self: TT, key: Data): Option[Int] = self match {
    case TT(v) if p(key) => Some(v)
    case _ => None()
  }

  def main(cont: TT, key: Data): Unit = get_mut(cont, key) match {
    case Some(v) => v.value = 1000
    case _ => ()
  }

}
