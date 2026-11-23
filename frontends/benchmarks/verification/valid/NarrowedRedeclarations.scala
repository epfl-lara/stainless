import stainless.lang._

object NarrowedRedeclarations {
  sealed abstract class Animal {
    def mate: Animal
    def legs(extra: BigInt): BigInt
  }

  // Redeclares `mate` and `legs`, narrowing the return type of `mate`
  sealed abstract class Bird extends Animal {
    def mate: Bird
    def legs(extra: BigInt): BigInt
  }

  case class Duck(m: Option[Duck]) extends Bird {
    def mate: Bird = m.getOrElse(this)
    def legs(extra: BigInt): BigInt = 2 + extra
  }

  case class Owl(age: BigInt) extends Bird {
    def mate: Bird = this
    def legs(extra: BigInt): BigInt = 2 + extra
  }

  case class Dog(age: BigInt) extends Animal {
    def mate: Animal = this
    def legs(extra: BigInt): BigInt = 4 + extra
  }

  // The calls through `Bird` and through `Animal` are the same call
  def sameMate(b: Bird): Unit = {
    val a: Animal = b
    assert(a.mate == b.mate)
  }

  def sameLegs(b: Bird, n: BigInt): Unit = {
    val a: Animal = b
    assert(a.legs(n) == b.legs(n))
    assert(b.legs(n) == 2 + n)
  }

  def birdMate(b: Bird): Unit = {
    val a: Animal = b
    assert(a.mate.isInstanceOf[Bird])
  }

  def dogLegs(d: Dog): Unit = {
    val a: Animal = d
    assert(a.legs(1) == 5)
  }

  // Stacked overrides that call `super`, mixed in two orders
  abstract class Base {
    def name(x: BigInt): BigInt = x
  }

  trait Plus1 extends Base {
    override def name(x: BigInt): BigInt = super.name(x) + 1
  }

  trait Times2 extends Base {
    override def name(x: BigInt): BigInt = super.name(x) * 2
  }

  case class PlusThenTimes() extends Plus1 with Times2
  case class TimesThenPlus() extends Times2 with Plus1

  def stacked(x: BigInt): Unit = {
    val b1: Base = PlusThenTimes()
    val b2: Base = TimesThenPlus()
    assert(b1.name(x) == (x + 1) * 2)
    assert(b2.name(x) == x * 2 + 1)
  }
}
