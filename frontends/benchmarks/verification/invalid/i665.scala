object i665:

  sealed abstract class A

  case class C() extends A

  case class D() extends A

  def m[T <: A](a: T): Boolean =
    a match
      case C() => true
      case D() => false

  def alwaysC[T <: A](a: T): Unit =
    assert(m(a))
