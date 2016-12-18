import stainless.lang._

object Array8 {

  def bar(): Boolean = {
    val a = foo()
    a.length == 5
  }.holds

  @inline
  def foo(): Array[Int] = {
    Array.fill(5)(0)
  } ensuring { res => res(0) == 0 }

}
