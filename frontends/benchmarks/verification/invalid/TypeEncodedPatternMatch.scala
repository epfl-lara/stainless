import stainless.lang._

// Type encoding refines the type arguments of the `C` pattern in `count`,
// while the counterexample from the solver only has erased types
object TypeEncodedPatternMatch {
  sealed abstract class L[T]
  case class C[T](h: T, t: L[T]) extends L[T]
  case class N[T]() extends L[T]

  abstract class A
  case class B(x: BigInt) extends A

  def count[T](l: L[T]): BigInt = l match {
    case C(h, t) => (if (h.isInstanceOf[B]) BigInt(1) else BigInt(0)) + count(t)
    case N() => BigInt(0)
  }

  def test(l: L[A]): Boolean = {
    count(l) < 2
  }.holds
}
