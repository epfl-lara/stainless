
import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.lang.StaticChecks._

object Examples {
  final case class Node private (var value: BigInt, var nextOpt: Option[Node], var repr: List[AnyHeapRef]) extends AnyHeapRef {
    def valid: Boolean = {
      reads(repr.content)
      decreases(repr.size)

      (nextOpt match {
        case None() => repr == List(this)
        case Some(next) => repr == this :: next.repr && next.valid
      })
    }

    def size: BigInt = {
      reads(repr.content)
      require(valid)
      decreases(repr.size)

      nextOpt match {
        case None() => BigInt(1)
        case Some(next) => 1 + next.size
      }
    } ensuring (res => res > 0)

    def last: Node = {
      reads(repr.content)
      require(valid)
      decreases(size)

      nextOpt match {
        case None() => this
        case Some(next) => next.last
      }
    }

    @extern
    def assume(b: Boolean): Unit = {
      ()
    } ensuring (_ => b)

    def append(node: Node): Unit = {
      reads(repr.content)
      modifies(repr.content)
      require(valid && node.valid && (repr.content & node.repr.content).isEmpty)
      decreases(size)

      nextOpt match {
        case None() => nextOpt = Some(node)
        case Some(next) => next.append(node)
      }

      repr = repr ++ node.repr

      // We would now like to prove that the size has increased by node.size, but I haven't found a way yet
    } ensuring (_ => valid)
  }

  def readInvariant(l1: Node, l2: Node): Unit = {
    reads(l1.repr.content ++ l2.repr.content)
    modifies(Set(l2))
    require(l1.valid && l2.valid && (l1.repr.content & l2.repr.content).isEmpty)
    val h1 = l1.value
    l2.value += 1
    val h2 = l1.value
    assert(h1 == h2)
  }
}
