import stainless.lang._

object ObjectHierarchyMutation7 {

  case class A(var x: Int, var y: Int)
  case class B(a1: A, a2: A)
  case class C(b1: B, b2: B)

  def updateB(b: B): Unit = {
    b.a1.x = 43
  }

  def update(c: C): Int = {
    updateB(c.b2)
    c.b2.a1.x
 }.ensuring(res => res == 43)

}
