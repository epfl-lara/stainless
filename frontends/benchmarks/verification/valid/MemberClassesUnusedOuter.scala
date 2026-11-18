import stainless.lang._

object MemberClassesUnusedOuter {
  class Box[V](val default: V) {
    case class Item(v: V)
  }

  def isItemOf[V](b: Box[V], e: Any): Boolean = e match {
    case b.Item(_) => true
    case _ => false
  }

  def same[V](b: Box[V], v: V): Unit = {
    assert(isItemOf(b, b.Item(v)))
  }

  // Neither `Values` nor its member classes are used by the functions above
  trait Values[V] {
    abstract class Value
    case class Const(v: V) extends Value
  }
}
