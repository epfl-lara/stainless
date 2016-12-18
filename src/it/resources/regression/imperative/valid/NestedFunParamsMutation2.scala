import stainless.lang._

object NestedFunParamsMutation2 {

  def f(): Int = {
    def g(a: Array[Int]): Unit = {
      require(a.length > 0)
      a(0) = 10
    }

    def h(a: Array[Int]): Unit = {
      require(a.length > 0)
      g(a)
    }

    val a = Array(1,2,3,4)
    h(a)
    a(0)
  } ensuring(_ == 10)

}
