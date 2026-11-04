import stainless.collection.*
import stainless.lang.*

object StrictEquality5:
  def same[T](x: T, y: T)(using CanEqual[T, T]): Boolean = x == y

  def test(): Boolean = same[Any](5: Byte, 5)

  def list(l: List[Any]): Boolean = l.contains(1)

  def set(s: Set[Any]): Boolean = s.contains(1)

  case class Box[T](x: T) derives CanEqual

  def boxes(a: Box[Any], b: Box[Any]): Boolean = a == b
