import stainless.lang._

object NestedFunParamsMutation1 {

  def f(): Int = {
    def g(a: Array[Int]): Unit = {
      require(a.length > 0)
      a(0) = 10
    }

    val a = Array(1,2,3,4)
    g(a)
    a(0)
  } ensuring(_ == 10)

}
