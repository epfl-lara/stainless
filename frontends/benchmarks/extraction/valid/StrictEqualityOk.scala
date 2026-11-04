import stainless.collection.*
import stainless.lang.*

object StrictEqualityOk:
  def same[T](x: T, y: T)(using CanEqual[T, T]): Boolean = x == y

  def numbers(): Boolean = same[Int](5, 5) && same[BigInt](1, 1) && same[(Int, Char)]((1, 'a'), (1, 'a'))

  case class Box[T](x: T) derives CanEqual

  def boxes(a: Box[Int], b: Box[Int]): Boolean = a == b && same(a, b)

  def wildcard(b: Box[?]): Boolean = true

  sealed abstract class Shape derives CanEqual
  case class Circle(r: BigInt) extends Shape
  case class Square(side: BigInt) extends Shape

  def shapes(x: Shape, y: Circle): Boolean = x == y

  def lists(l: List[BigInt]): Boolean = l.contains(1) && l == Nil[BigInt]() && (l ++ l).reverse == l

  def options(o: Option[Box[Int]]): Boolean = o == None[Box[Int]]()

  // Values of type `Any` are fine as long as they are not compared
  case class Holder(a: Any)

  def holder(h: Holder): Boolean = h.a.isInstanceOf[Int]

  def literal(x: BigInt): Boolean = x match
    case 5 => true
    case _ => false
