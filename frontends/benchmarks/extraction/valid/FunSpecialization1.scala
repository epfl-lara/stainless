import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.lang.StaticChecks._

object FunSpecialization1Example {
  def concat[T](xs: List[T], ys: List[T]): List[T] = {
    xs match {
      case Nil() => ys
      case Cons(x, xs) => Cons(x, concat(xs, ys))
    }
  } ensuring (res => res.size == xs.size + ys.size)

  def concatBigInt(xs: List[BigInt], ys: List[BigInt]): List[BigInt] =
    specialize(concat[BigInt](xs, ys))

  def snoc[T](xs: List[T], y: T): List[T] =
    specialize(concat(xs, List(y)))

  // Fails because original, non-specialized parameters must come first
  // def snocBad[T](y: T, xs: List[T]): List[T] =
  //   specialize(concat(xs, List(y)))

  // Fails because `xs` varies in the recursive calls of `concat`
  // def cons[T](xs: List[T], y: T): List[T] =
  //   specialize(concat(List(y), xs))


  def forallL[T](xs: List[T], f: T => Boolean): Boolean =
    xs match {
      case Nil() => true
      case Cons(x, xs) => f(x) && forallL(xs, f)
    }

  def forallLBigInt(xs: List[BigInt], f: BigInt => Boolean): Boolean =
    specialize(forallL(xs, f))

  def forallLPos(xs: List[BigInt]): Boolean =
    specialize(forallL[BigInt](xs, _ > 0))


  @opaque
  @template
  def forallImpliedL[T](xs: List[T], f: T => Boolean, g: T => Boolean): Unit = {
    require(forallL(xs, f))
    assert(forall((x: T) => f(x) ==> g(x))) // Will be proven for specializations
    if (xs.nonEmpty) {
      assert(f(xs.head) ==> g(xs.head))
      forallImpliedL(xs.tail, f, g)
    }
  } ensuring (_ => forallL(xs, g))

  def posIsNonNegL(xs: List[BigInt]): Unit =
    specialize(forallImpliedL[BigInt](xs, _ > 0, _ >= 0))
}
