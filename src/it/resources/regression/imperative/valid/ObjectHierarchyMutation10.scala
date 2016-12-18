import stainless.lang._

object ObjectHierarchyMutation10 {

  case class A(var x: Int)
  case class B(a1: A, a2: A)

  def updateB(b: B): Unit = {
    b.a1.x = 42
    b.a2.x = 41
  }

  def updateA(a1: A, a2: A): Unit = {
    updateB(B(a1, a2))
  } ensuring(_ => a1.x == 42 && a2.x == 41)

}
