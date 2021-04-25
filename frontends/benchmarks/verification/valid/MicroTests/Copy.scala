import stainless.lang._

object Copy {

  case class A(x: BigInt, b: B)
  case class B(y: BigInt, c: C)
  case class C(z: BigInt)

  def double(a: A): A = {
    a.copy(
      x = a.x * 2,
      b = a.b.copy(
        y = a.b.y * 2,
        c = a.b.c.copy(z = a.b.c.z * 2)
      )
    )
  }

  def sum(a: A): BigInt = {
    a.x + a.b.y + a.b.c.z
  }

  def prop(a: A) = (sum(a) * 2 == sum(double(a))).holds

}
