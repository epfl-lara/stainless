import stainless.lang._

object ObjectHierarchyMutation8 {

  case class A(var x: Int)
  case class B(a: A)

  def updateB(b: B): Unit = {
    b.a.x = 42
  }

  def updateA(a: A): Unit = {
    updateB(B(a))
  } ensuring(_ => a.x == 42)

}
