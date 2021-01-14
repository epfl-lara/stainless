import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.lang.StaticChecks._

object MutListSetsOnlyExample {
  final case class Node private (
    var value: BigInt,
    var nextOpt: Option[Node],
    var repr: Set[AnyHeapRef]
  ) extends AnyHeapRef {

    @ghost
    def valid: Boolean = {
      reads(repr ++ Set(this))

      val no = nextOpt; no match {
        case None() =>
          // size == 1 &&
          repr == Set(this)
        case Some(next) =>
          // repr == next.repr +!+ Set(this) &&
          (repr == next.repr ++ Set(this) : Boolean) &&
          (!next.repr.contains(this) : Boolean) &&
          next.valid
      }
    }

    @ghost
    def lemmaValidNextValid: Boolean = {
      reads(repr ++ Set(this))
      (valid && nextOpt.isDefined) ==> nextOpt.get.valid
    } ensuring (res => res)

    def append(node: Node): Unit = {
      reads(repr ++ node.repr ++ Set(this, node))
      modifies(repr ++ Set(this))
      require(valid && node.valid && (repr & node.repr).isEmpty)

      val no = nextOpt; no  match {
        case None() =>
          nextOpt = Some(node)
          repr = node.repr ++ Set(this)

        case Some(next) =>
          assert(!(this == next))
          assert(next.valid)
          val preRepr = repr ++ node.repr
          val preReprN = next.repr ++ node.repr
          assert(preRepr == preReprN ++ Set(this))

          val oldRepr = repr
          assert(oldRepr.subsetOf(preRepr))

          next.append(node)

          repr = next.repr ++ Set(this)

          assert(valid)
      }

    } ensuring { _ =>
      (old(nextOpt.isInstanceOf[Some[AnyHeapRef]]) ==> (nextOpt == old(nextOpt))) &&
      repr == old(repr ++ node.repr) &&
      valid
    }
  }
}
