import stainless.lang._

object ObjectHierarchyMutation11 {

  case class A(var x: Int)
  case class B(a: A, y: Int)

  def updateB(b1: B, b2: B): Unit = {
    b1.a.x = 42
    b2.a.x = 41
  }

  def update(a1: A, a2: A, y: Int): Unit = {
    updateB(B(a2, y), B(a1, y))
  } ensuring(_ => a2.x == 42 && a1.x == 41)

}
