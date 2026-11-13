object i839c:

  case class A() {}

  case class B(a: A = A())

  case class C():
    val b = B(A())
