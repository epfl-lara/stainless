import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.lang.StaticChecks._

object FunSpecialization1Example {
  def concat[T](xs: List[T], ys: List[T]): List[T] =
    xs match {
      case Nil() => ys
      case Cons(x, xs) => Cons(x, concat(xs, ys))
    }

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

  // We can also strengthen the pre- and postcondition
  def snocStrong[T](xs: List[T], y: T): List[T] = {
    specialize(concat(xs, List(y)))
 }.ensuring { _.size >= 1 }

  def concatSized1[T](xs: List[T], ys: List[T]): List[T] = {
    specialize(concat(xs, ys))
 }.ensuring(res => res.size == xs.size + ys.size)

  def concatWithProp1[T](xs: List[T], ys: List[T], f: T => Boolean): List[T] = {
    require(xs.forall(f) && ys.forall(f))
    specialize(concat(xs, ys))
 }.ensuring { _.forall(f) }


  // We don't have to specialize the function definitions themselves to prove things about them.
  // Instead, one can define "proof templates" like so:
  @template
  def concatInductiveProof[T](xs: List[T], ys: List[T]): Unit =
    xs match {
      case Nil() => true
      case Cons(x, xs) => concatInductiveProof(xs, ys)
    }

  def concatSized2[T](xs: List[T], ys: List[T]): Unit = {
    specialize(concatInductiveProof[T](xs, ys))
 }.ensuring { _ => concat(xs, ys).size == xs.size + ys.size }

  def concatWithProp2[T](xs: List[T], ys: List[T], f: T => Boolean): List[T] = {
    require(xs.forall(f) && ys.forall(f))
    specialize(concat(xs, ys))
 }.ensuring { _ => concat(xs, ys).forall(f) }

  def concatAssoc[T](xs: List[T], ys: List[T], zs: List[T]): List[T] = {
    specialize(concat(xs, ys))
 }.ensuring { _ => concat(concat(xs, ys), zs) == concat(xs, concat(ys, zs)) }


  // Some more examples

  def forallL[T](xs: List[T], f: T => Boolean): Boolean =
    xs match {
      case Nil() => true
      case Cons(x, xs) => f(x) && forallL(xs, f)
    }

  def forallLBigInt(xs: List[BigInt], f: BigInt => Boolean): Boolean =
    specialize(forallL(xs, f))

  def forallLPos(xs: List[BigInt]): Boolean =
    specialize(forallL[BigInt](xs, _ > 0))


  @template
  def forallImpliedL[T](xs: List[T], f: T => Boolean, g: T => Boolean): Unit = {
    require(forallL(xs, f))
    if (xs.nonEmpty) {
      assert(f(xs.head) ==> g(xs.head)) // Will be proven for specializations
      forallImpliedL(xs.tail, f, g)
    }
 }.ensuring(_ => forallL(xs, g))

  def posIsNonNegL(xs: List[BigInt]): Unit =
    specialize(forallImpliedL[BigInt](xs, _ > 0, _ >= 0))
}
