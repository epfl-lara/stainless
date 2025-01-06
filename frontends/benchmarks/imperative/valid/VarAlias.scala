object VarAlias {

  case class A(data: Array[Int])

  def f(a: A): Unit = {
    require(a.data.length > 0)

    a.data(0) = 10

 }.ensuring(_ =>
    a.data.length > 0
  )

  def g() = {
    val data = Array(100)
    val a = A(data)
    f(a)
    assert(a.data(0) == 10)
  }

}
