import stainless.lang._

object ConcreteParents {
  class C(val x: BigInt) {
    def m: BigInt = x + 1
  }
  case class D(y: BigInt) extends C(y * 2) {
    override def m: BigInt = y
  }
  case object O extends C(10)

  def plain: Unit = {
    val c = new C(5)
    assert(c.m == 6)
    assert(c.x == 5)
    val d: C = D(3)
    assert(d.x == 6)
    assert(d.m == 3)
    assert(O.x == 10 && O.m == 11)
  }

  // A chain of concrete classes, with invariants and a plain constructor parameter
  sealed class A(val n: BigInt) {
    require(n >= 0)
    def size: BigInt = n
  }
  sealed class B(k: BigInt) extends A(k + 1) {
    def k2: BigInt = k
  }
  final case class E(j: BigInt) extends B(2 * j) {
    require(j >= 0)
    override def size: BigInt = j
  }
  case object Z extends A(0)

  def sizes(a: A): BigInt = {
    a match {
      case e: E => assert(e.n == 2 * e.j + 1)
      case b: B => assert(b.n == b.k2 + 1)
      case Z => assert(Z.n == 0)
      case _ => ()
    }
    a.size
  }.ensuring(_ >= 0)

  def nonNegative(a: A): Unit = {
    assert(a.n >= 0)
  }

  def chain: Unit = {
    assert(new A(3).size == 3)
    assert(new B(3).n == 4)
    assert(E(3).n == 7)
    assert(E(3).size == 3)
  }

  // Type parameters, and patterns on a case class with a concrete parent
  class Box[T](val value: T)
  case class IntBox(i: Int) extends Box[Int](i)
  def unbox(b: Box[Int]): Int = b match {
    case IntBox(i) => assert(b.value == i); i
    case _ => b.value
  }

  // Default arguments
  class WithDefault(val x: BigInt = 7)
  case class UsesDefault() extends WithDefault()
  def defaults: Unit = {
    assert(new WithDefault().x == 7)
    assert(UsesDefault().x == 7)
  }

  // Exceptions with concrete classes in their hierarchy
  class SolverError(msg: String) extends Exception
  case class RuntimeError(message: String) extends SolverError("Runtime error: " + message)
  case class TypeMismatch(n: BigInt) extends SolverError("Type mismatch")

  def isSolverError(e: Exception): Boolean = e match {
    case _: SolverError => true
    case _ => false
  }

  def exceptions: Unit = {
    assert(isSolverError(RuntimeError("x")))
    assert(isSolverError(TypeMismatch(1)))
    assert(isSolverError(new SolverError("x")))
  }
}
