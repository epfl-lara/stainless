import stainless.collection.*
import stainless.lang.*

object AnyEquality3:
  def same[T](x: T, y: T): Boolean = x == y

  def viaCall[T](x: T, y: T): Boolean = same(x, y)

  def test(): Boolean = same[Any](5: Byte, 5) && viaCall[Any](1, 2)

  def list(l: List[Any]): Boolean = l.contains(1)

  def local(): Boolean =
    def inner[T](x: T, y: T): Boolean = x == y
    inner[Any](1, 2)
