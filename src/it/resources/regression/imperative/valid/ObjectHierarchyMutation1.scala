import stainless.lang._

object ObjectHierarchyMutation1 {

  case class A(var y: Int)
  case class B(a: A)

  def update(b: B): Int = {
    b.a.y = 17
    b.a.y
  } ensuring(res => res == 17)

}
