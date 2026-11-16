import stainless.lang._

object GenericSortInvariants {
  // An open class, so that `Lang[V]` values are encoded along with the type parameter `V`
  trait Lang[V] {
    def default: V
  }
  case class Ints() extends Lang[BigInt] {
    def default: BigInt = 0
  }

  def compatible[V](l1: Lang[V], l2: Lang[V]): Boolean = l1.default == l2.default

  sealed abstract class Expr[V] {
    def lang: Lang[V] = this match {
      case Lit(l, _) => l
      case Pair(l, _, _) => l
    }
  }
  case class Lit[V](l: Lang[V], v: V) extends Expr[V]
  // The invariant of `Pair` mentions the open class type `Lang[V]`
  case class Pair[V](l: Lang[V], left: Expr[V], right: Expr[V]) extends Expr[V] {
    require(compatible(left.lang, l) && compatible(right.lang, l))
  }

  def size[V](e: Expr[V]): BigInt = {
    decreases(e)
    e match {
      case Lit(_, _) => BigInt(1)
      case Pair(_, l, r) => size(l) + size(r)
    }
  }.ensuring(_ > 0)

  def test: Unit = {
    val ints = Ints()
    val e = Pair[BigInt](ints, Lit(ints, 1), Lit(ints, 2))
    assert(e.left.lang.default == 0)
    assert(size(e) == 2)
  }
}
