import stainless.lang._

object ObjectHierarchyMutation2 {

  case class A(var y: Int)
  case class B(a: A)

  def update(b: B): Int = {
    b.a.y = 17
    b.a.y
  }

  def f(): Int = {
    val b = B(A(10))
    update(b)
    b.a.y
  } ensuring(res => res == 17)

}
