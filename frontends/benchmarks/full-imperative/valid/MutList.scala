
import stainless.annotation.{ghost => ghostAnnot, _}
import stainless.collection._
import stainless.lang._
import stainless.lang.Option._
import stainless.lang.StaticChecks._
import stainless.proof.check

object MutListExample {
  final case class Node private (var value: BigInt, var nextOpt: Option[Node], @ghostAnnot var repr: List[AnyHeapRef]) extends AnyHeapRef {
    @ghostAnnot
    def valid: Boolean = {
      reads(repr.content ++ Set(this))
      decreases(repr.size)

      nextOpt match {
        case None() =>
          repr == List(this)
        case Some(next) =>
          repr.content.contains(next) &&
          repr == this :: next.repr &&
          repr.content == next.repr.content ++ Set(this) &&
          !next.repr.content.contains(this) &&
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

    @opaque
    def append(node: Node): Unit = {
      reads(repr.content ++ node.repr.content ++ Set(this, node))
      modifies(repr.content ++ Set(this))
      require(valid && node.valid && (repr.content & node.repr.content).isEmpty)
      decreases(size)

      @ghostAnnot val oldRepr = repr
      @ghostAnnot val oldReprConcat = repr ++ node.repr
      @ghostAnnot val oldReprConcatContents = repr.content ++ node.repr.content

      nextOpt match {
        case None() =>
          nextOpt = Some(node)
          repr = this :: node.repr
          @ghostAnnot val unused1 = check(valid)
          @ghostAnnot val unused2 = check(repr == oldReprConcat)
          @ghostAnnot val unused3 = check(repr.content == oldReprConcatContents)

        case Some(next) =>
          assert(next.valid)
          assert(next.repr.content subsetOf repr.content)

          @ghostAnnot val oldReprNext = next.repr
          @ghostAnnot val oldReprC = next.repr.content ++ node.repr.content

          next.append(node)

          assert(next.repr.content == oldReprC)
          assert(next.valid)

          repr = this :: next.repr

          assert(next.repr.content subsetOf repr.content)
          assert(repr == this :: (oldReprNext ++ node.repr))
          assert(repr == (this :: oldReprNext) ++ node.repr)
          ghost { check(repr == oldRepr ++ node.repr) }
      }
    } ensuring { _ => valid &&& repr == old(repr ++ node.repr) &&& repr.content == old(repr.content ++ node.repr.content) }
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
