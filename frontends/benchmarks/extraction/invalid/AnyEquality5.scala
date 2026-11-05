object AnyEquality5:
  abstract class Container[A]:
    def elem: A
    def holds(x: A): Boolean = elem == x

  case class IntContainer(elem: Int) extends Container[Int]

  case class AnyContainer(elem: Any) extends Container[Any]

  def test(c: Container[Any]): Boolean = c.holds(1)

  sealed abstract class Base[A]
  case class Derived[A, B](a: A, b: B) extends Base[A]

  def compare(x: Base[Int], y: Base[Int]): Boolean = x == y

  def build(): Base[Int] = Derived[Int, Any](1, 2)
