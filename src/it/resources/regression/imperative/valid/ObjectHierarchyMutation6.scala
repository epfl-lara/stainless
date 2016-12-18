import stainless.lang._

object ObjectHierarchyMutation6 {

  case class A(var x: Int, var y: Int)
  case class B(a1: A, a2: A)
  case class C(b1: B, b2: B)

  def updateA(a: A): Unit = {
    a.x = 43
  }

  def update(c: C): Int = {
    updateA(c.b2.a1)
    c.b2.a1.x
  } ensuring(res => res == 43)

}
