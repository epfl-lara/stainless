import stainless.lang._

object GenericOuters {
  class Box[V](val default: V) {
    case class Item(v: V)
  }

  def mk[V](v: V): Box[V] = new Box(v)

  def isItemOf[V](b: Box[V], e: Any): Boolean = e match {
    case b.Item(_) => true
    case _ => false
  }

  // Scala compares outer instances by reference
  def structural: Unit = {
    val a = mk[BigInt](1)
    val b = mk[BigInt](1)
    assert(isItemOf(a, b.Item(0)))
  }

  // The instances may be the same
  def unknown[V](b1: Box[V], b2: Box[V], v: V): Unit = {
    assert(!isItemOf(b2, b1.Item(v)))
  }
}
