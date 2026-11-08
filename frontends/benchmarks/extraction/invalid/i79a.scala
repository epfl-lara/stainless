object i79a:

  case class A()

  def equals(a1: A, a2: A): Boolean = true

  case class B()

  case class Table():
    def foo(a: A, b: B) = equals(a, b)
