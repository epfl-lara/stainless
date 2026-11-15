object i665:

  sealed abstract class A

  case class C() extends A

  case class D() extends A

  def f[T <: A](a: T): Boolean =
    a.isInstanceOf[C]

  def m[T <: A](a: T): Boolean =
    a match
      case C() => true
      case D() => false

  def typed[T <: A](a: T): Boolean =
    a match
      case _: C => true
      case _ => false

  def onC(c: C): Unit =
    assert(f(c))
    assert(m(c))
    assert(typed(c))

  def onD(d: D): Unit =
    assert(!f(d))
    assert(!m(d))
    assert(!typed(d))

  def agree[T <: A](a: T): Unit =
    assert(f(a) == m(a))
    assert(m(a) == typed(a))
