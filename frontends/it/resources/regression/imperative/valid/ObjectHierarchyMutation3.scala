import stainless.lang._

object ObjectHierarchyMutation3 {

  case class A(var x: Int, var y: Int, var z: Int)
  case class B(a1: A, a2: A, a3: A)

  def update(b: B): Int = {
    b.a2.y = 17
    b.a2.y
  } ensuring(res => res == 17)

  def f(): Int = {
    val b = B(A(10, 11, 12), A(11, 12, 13), A(13, 14, 15))
    update(b)
    b.a2.y
  } ensuring(res => res == 17)

}
