import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.lang.Option._
import stainless.lang.StaticChecks._
import stainless.proof.check

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
          repr == Set(this)
        case Some(next) =>
          // repr == next.repr +!+ Set(this) &&
          repr.contains(next) &&
          (repr == next.repr ++ Set(this) : Boolean) &&
          (!next.repr.contains(this) : Boolean) &&
          next.valid
      }
    }

    def append(node: Node): Unit = {
      reads(repr ++ node.repr ++ Set(this, node))
      modifies(repr ++ Set(this))
      require(valid && node.valid && (repr & node.repr).isEmpty)

      val no = nextOpt; no  match {
        case None() =>
          nextOpt = Some(node)
          repr = node.repr ++ Set(this)

        case Some(next) =>
          assert(next.valid)
          next.append(node)
          repr = next.repr ++ Set(this)
          @ghost val unused = check(valid)
      }

    } ensuring { _ =>
      repr == old(repr ++ node.repr) &&
      valid
    }
  }
}
