import stainless.lang._

object ObjectHierarchyMutation5 {

  case class A(var x: Int)
  case class B(a: A)
  case class C(b: B)

  def updateA(a: A): Unit = {
    a.x = 43
  }

  def update(c: C): Int = {
    updateA(c.b.a)
    c.b.a.x
  } ensuring(res => res == 43)

}
