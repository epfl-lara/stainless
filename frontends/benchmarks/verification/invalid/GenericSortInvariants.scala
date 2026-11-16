import stainless.lang._

object GenericSortInvariants {
  // An open class, so that `Lang[V]` values are encoded along with the type parameter `V`
  trait Lang[V] {
    def default: V
  }
  case class Ints(default: BigInt) extends Lang[BigInt]

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

  def incompatible: Unit = {
    val e = Pair[BigInt](Ints(0), Lit(Ints(1), 1), Lit(Ints(0), 2))
  }
}
