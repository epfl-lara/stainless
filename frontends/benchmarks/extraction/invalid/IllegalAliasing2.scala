object IllegalAliasing2 {

  case class A(var x: Int)
  def f(a1: A, a2: A): Unit = {
  }

  def zero: Int = 0

  def g(a: Array[A]) = {
    require(a.length > 0)

    f(a(0), a(zero)) // Illegal passing of aliased parameters
  }

}
