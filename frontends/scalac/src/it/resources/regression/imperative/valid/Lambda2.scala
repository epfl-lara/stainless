
object Lambda2 {

  /*
   * The tricky thing here is that there is a lambda with a mutable type as a parameter,
   * but the implementation does not mutate it in any way.
   */

  case class A(var x: Int)

  def test: Int = {
    val f: (A) => Int = ((a: A) => a.x)
    f(A(0))
  } ensuring(res => res == 0)

}
