object Copy {

  case class A(a: Int, b: Int)

  def f(a: A): A = {
    a.copy(b = 17)
  } ensuring(res => res.a == a.a && res.b == 17)

  def g(a: A): A = {
    a.copy(b = 17)
  } ensuring(res => res.a == a.a)

  def h(a: A): A = {
    a.copy(b = 17)
  } ensuring(res => res.b == 17)
}
