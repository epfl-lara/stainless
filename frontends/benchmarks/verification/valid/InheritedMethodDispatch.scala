import stainless.lang._

object InheritedMethodDispatch {

  // `get` is inherited through an open intermediate class that only declares an abstract val
  abstract class Container {
    def get: BigInt = 1
  }

  abstract class Named extends Container {
    val name: BigInt
  }

  case class IntNamed(name: BigInt) extends Named

  abstract class Labeled extends Named {
    def label: BigInt = name + get
  }

  case class IntLabeled(name: BigInt) extends Labeled

  case class Overriding(name: BigInt) extends Named {
    override def get: BigInt = name
  }

  def nameOf(n: Named): BigInt = n.name

  def getOf(c: Container): BigInt = c.get

  def testOpen: Unit = {
    val n = IntNamed(2)
    assert(n.get == 1)
    assert(getOf(n) == 1)
    assert(nameOf(n) == 2)

    val l = IntLabeled(3)
    assert(l.get == 1)
    assert(getOf(l) == 1)
    assert(l.label == 4)

    val o = Overriding(5)
    assert(o.get == 5)
    assert(getOf(o) == 5)
  }

  // In a sealed hierarchy, `D` inherits `f` through `B` while its sibling `C` and its uncle `E` override it
  sealed abstract class A {
    def f: BigInt = 1
  }

  sealed abstract class B extends A

  case class C() extends B {
    override def f: BigInt = 2
  }

  case class D() extends B

  case class E() extends A {
    override def f: BigInt = 3
  }

  def fOf(a: A): BigInt = a.f

  def testSealed: Unit = {
    assert(fOf(C()) == 2)
    assert(fOf(D()) == 1)
    assert(fOf(E()) == 3)
  }

  def fOfB(b: B): BigInt = {
    b.f
  }.ensuring(res => res == 1 || res == 2)
}
