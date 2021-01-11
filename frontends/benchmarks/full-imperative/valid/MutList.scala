
import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.lang.StaticChecks._

object MutListExample {
  final case class Node private (var value: BigInt, var nextOpt: Option[Node], @ghost var repr: List[AnyHeapRef]) extends AnyHeapRef {
    @ghost
    def valid: Boolean = {
      reads(repr.content ++ Set(this))
      decreases(repr.size)

      nextOpt match {
        case None() =>
          repr == List(this)
        case Some(next) =>
          repr.nonEmpty && repr.tail.nonEmpty && repr.tail.head == next && // "next ∈ repr"
          repr == this :: next.repr &&
          next.valid
      }
    }

    def size: BigInt = {
      reads(repr.content ++ Set(this))
      require(valid)
      decreases(repr.size)

      nextOpt match {
        case None() => BigInt(1)
        case Some(next) => 1 + next.size
      }
    } ensuring (_ > 0)

    def last: Node = {
      reads(repr.content ++ Set(this))
      require(valid)
      decreases(size)

      nextOpt match {
        case None() => this
        case Some(next) => next.last
      }
    }

    def append(node: Node): Unit = {
      reads(repr.content ++ node.repr.content ++ Set(this, node))
      modifies(repr.content ++ Set(this))
      require(valid && node.valid && (repr.content & node.repr.content).isEmpty)
      decreases(size)

      nextOpt match {
        case None() =>
          nextOpt = Some(node)
          repr = this :: node.repr
        case Some(next) =>
          next.append(node)
          repr = this :: next.repr
      }

      // We would now like to prove that the size has increased by node.size, but I haven't found a way yet
    } ensuring (_ => valid)
  }

  def readInvariant(l1: Node, l2: Node): Unit = {
    reads(l1.repr.content ++ l2.repr.content ++ Set(l1, l2))
    modifies(Set(l2))
    require(l1.valid && l2.valid && (l1.repr.content & l2.repr.content).isEmpty)
    val h1 = l1.value
    l2.value += 1
    val h2 = l1.value
    assert(h1 == h2)
  }
}
