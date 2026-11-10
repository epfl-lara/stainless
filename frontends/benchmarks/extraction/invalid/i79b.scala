object i79b:

  case class A()

  case class B()

  case class Table():
    def foo(a: A, b: B) = this.equals((a, b))
