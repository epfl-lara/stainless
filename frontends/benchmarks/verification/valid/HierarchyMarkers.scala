import stainless.lang._

object HierarchyMarkers {
  // An unsealed trait mixed into the classes of two sealed hierarchies
  trait Named {
    def name: BigInt
  }

  sealed abstract class Shape
  case class Circle(r: BigInt) extends Shape with Named {
    def name: BigInt = 1
  }
  case class Square(s: BigInt) extends Shape

  sealed abstract class Animal
  case class Dog(age: BigInt) extends Animal with Named {
    def name: BigInt = 2
  }
  case class Cat() extends Animal

  def nameOf(n: Named): BigInt = n.name

  def names: Unit = {
    assert(nameOf(Circle(1)) == 1)
    assert(nameOf(Dog(3)) == 2)
  }

  def tests(x: Any): Unit = {
    val a: Any = Circle(2)
    assert(a.isInstanceOf[Named])
    assert(a.isInstanceOf[Shape])
    assert(!a.isInstanceOf[Animal])

    val n: Named = Dog(1)
    assert(n.isInstanceOf[Animal])
    assert(!n.isInstanceOf[Shape])
    n match {
      case Dog(age) => assert(age == 1)
      case _ => assert(false)
    }

    x match {
      case s: Shape => assert(!x.isInstanceOf[Animal])
      case Cat() => assert(!x.isInstanceOf[Named])
      case _ => ()
    }
  }

  def namedShape(s: Shape): Boolean = {
    s.isInstanceOf[Named]
  }.ensuring(res => res == s.isInstanceOf[Circle])

  // A class that extends two sealed roots puts them in one hierarchy
  sealed trait Left
  sealed trait Right
  case class Both(x: BigInt) extends Left with Right
  case class OnlyLeft() extends Left

  def isBoth(l: Left): Boolean = l match {
    case Both(_) => true
    case OnlyLeft() => false
  }

  def rightValue(r: Right): BigInt = r match {
    case Both(x) => x
  }

  def asRight(l: Left): BigInt = {
    require(isBoth(l))
    rightValue(l.asInstanceOf[Right])
  }
}
