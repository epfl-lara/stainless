import stainless.lang._

object Copy2 {

  case class A[T](x: BigInt, b: B[T])
  case class B[T](y: BigInt, c: C[T])
  case class C[T](z: T)

  def double[T](a: A[T]): A[T] = {
    a.copy(
      x = a.x * 2,
      b = a.b.copy(
        y = a.b.y * 2,
        c = a.b.c.copy(z = a.b.c.z)
      )
    )
  }

  def sum[T](a: A[T]): BigInt = {
    a.x + a.b.y
  }

  def prop[T](a: A[T]) = (sum(a) * 2 == sum(double(a))).holds

}
