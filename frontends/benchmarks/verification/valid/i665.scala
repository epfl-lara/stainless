object i665:

  sealed abstract class A

  case class C() extends A

  case class D() extends A

  def f[T <: A](a: T): Boolean =
    a.isInstanceOf[C]

  def isC(): Unit =
    assert(f(C()))

  def isNotC(): Unit =
    assert(!f(D()))
