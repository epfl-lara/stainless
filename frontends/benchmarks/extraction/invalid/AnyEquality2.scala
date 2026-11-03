import stainless.collection.*

object AnyEquality2:
  case class Box(a: Any)

  def boxes(x: Box, y: Box): Boolean = x == y

  sealed abstract class Shape
  case class Circle(r: BigInt) extends Shape
  case class Tagged(tag: Any) extends Shape

  def shapes(x: Shape, y: Shape): Boolean = x != y

  def tuples(x: (BigInt, Any), y: (BigInt, Any)): Boolean = x == y

  def lists(x: List[Int], y: List[Byte]): Boolean = x == y
