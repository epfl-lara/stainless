import stainless.lang._

object ObjectHierarchyMutation4 {

  case class A(var x: Int, var y: Int)
  case class B(a1: A, a2: A)
  case class C(b1: B, b2: B)

  def update(c: C): Int = {
    c.b1.a2.y = 17
    c.b1.a2.y
  } ensuring(res => res == 17)

  def f(): Int = {
    val c = C(B(A(10, 10), A(12, 13)), B(A(10, 10), A(14, 15)))
    update(c)
    c.b1.a2.y
  } ensuring(res => res == 17)

  def multipleUpdate(c: C): Unit = {
    c.b1.a2.y = 13
    c.b1.a2.x = 10
    c.b1.a1.x = 15
    c.b2.a1.y = 22
  } ensuring(_ => c.b1.a2.y == 13 && c.b1.a2.x == 10 && c.b1.a1.x == 15 && c.b2.a1.y == 22 && c.b2.a2.y == old(c).b2.a2.y)

}
