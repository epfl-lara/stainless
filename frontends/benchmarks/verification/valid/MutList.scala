
import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._

object Examples {
  final case class Node private (var content: BigInt, next: Option[Node], repr: List[AnyHeapRef]) extends AnyHeapRef {
    def valid: Boolean = {
      reads(repr.content)
      decreases(repr.size)

      (next match {
        case None() => repr == this :: Nil()
        case Some(next) => repr == this :: next.repr && !next.repr.contains(this) && next.valid
      })
    }

    def size: BigInt = {
      reads(repr.content)
      require(valid)
      decreases(repr.size)

      next match {
        case None() => 1
        case Some(next) => 1 + next.size
      }
    }
  }

  def readInvariant(l1: Node, l2: Node): Unit = {
    reads(l1.repr.content ++ l2.repr.content)
    modifies(Set(l2))
    require(l1.valid && l2.valid && (l1.repr.content & l2.repr.content).isEmpty)
    val h1 = l1.content
    l2.content += 1
    val h2 = l1.content
    assert(h1 == h2)
  }
}
