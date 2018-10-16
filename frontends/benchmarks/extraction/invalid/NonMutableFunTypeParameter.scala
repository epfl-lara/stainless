import stainless.annotation._

object NonMutableFunTypeParameter {
  def f[T](t: T) = t

  @mutable
  trait A

  // cannot instantiate f[T] with mutable type A
  def g(a: A) = f(a)
}
