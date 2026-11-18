import stainless.lang._
import stainless.collection._

object GenericOuters {
  // A language generic in the type of its literals
  trait Lang[V] {
    sealed abstract class Expr
    case class Lit(v: V) extends Expr
    case class Pair(l: Expr, r: Expr) extends Expr

    final def lits(e: Expr): List[V] = {
      decreases(e)
      e match {
        case Lit(v) => List(v)
        case Pair(l, r) => lits(l) ++ lits(r)
      }
    }

    final def size(e: Expr): BigInt = {
      decreases(e)
      e match {
        case Lit(_) => BigInt(1)
        case Pair(l, r) => size(l) + size(r)
      }
    }.ensuring(res => res > 0 && res == lits(e).size)
  }

  case object ints extends Lang[BigInt]
  case object bools extends Lang[Boolean]

  def convert(e: ints.Expr): bools.Expr = {
    decreases(e)
    e match {
      case ints.Lit(v) => bools.Lit(v > 0)
      case ints.Pair(l, r) => bools.Pair(convert(l), convert(r))
    }
  }

  def generic[V](l: Lang[V])(e: l.Expr): BigInt = l.size(e)

  def test: Unit = {
    val e = ints.Pair(ints.Lit(1), ints.Lit(-1))
    assert(ints.lits(e) == List[BigInt](1, -1))
    assert(bools.lits(convert(e)) == List(true, false))
    assert(generic(ints)(e) == 2)
  }

  // Instances of generic classes are compared by reference as outer instances
  class Box[V](val default: V) {
    case class Item(v: V) {
      // The outer instance of the new item is that of `this`
      def renew: Item = Item(v)
    }
  }

  def mk[V](v: V): Box[V] = new Box(v)

  def isItemOf[V](b: Box[V], e: Any): Boolean = e match {
    case b.Item(_) => true
    case _ => false
  }

  // The type of `i.v` is given by the outer instance `b`
  def value[V](b: Box[V], i: b.Item): V = i.v

  def distinct: Unit = {
    val a = mk[BigInt](1)
    val b = mk[BigInt](1)
    val i = a.Item(2)
    assert(isItemOf(a, i))
    assert(!isItemOf(b, i))
  }

  def same[V](b: Box[V], v: V): Unit = {
    assert(isItemOf(b, b.Item(v)))
    assert(isItemOf(b, b.Item(v).renew))
    assert(value(b, b.Item(v)) == v)
  }
}
