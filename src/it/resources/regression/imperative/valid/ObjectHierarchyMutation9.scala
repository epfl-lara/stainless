import stainless.lang._

object ObjectHierarchyMutation9 {

  case class A(var x: Int)
  case class B(a: A)

  def updateB(b1: B, b2: B): Unit = {
    b1.a.x = 42
    b2.a.x = 41
  }

  def updateA(a1: A, a2: A): Unit = {
    updateB(B(a1), B(a2))
  } ensuring(_ => a1.x == 42 && a2.x == 41)

}
