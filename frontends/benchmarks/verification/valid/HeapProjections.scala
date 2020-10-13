
import stainless.lang._
import stainless.annotation._

object Examples {
  final case class Box(var value: BigInt)

  @extern
  def pure(x: Box): Unit = {
    reads(Set(x))
    modifies(Set())
  }

  def usePure(x: Box): Unit = {
    pure(x)
  } ensuring { _ =>
    old(x) == x
  }
}
