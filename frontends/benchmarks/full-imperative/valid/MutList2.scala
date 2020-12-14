
import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.lang.StaticChecks._

object MutList2Example {
  case class MutList(root: Option[Node], var repr: List[AnyHeapRef]) extends AnyHeapRef {
    def validFrom(nodeOpt: Option[Node], repr: List[AnyHeapRef]): Boolean = {
      reads(repr.content ++ (if (nodeOpt.isDefined) Set(nodeOpt.get) else Set()))
      decreases(repr.size)

      // val repr_ = repr
      // repr_ match {
      //   case Nil() => false
      //   case Cons(reprNode, reprRest) => reprNode == node && validFrom()
      // }

      val no = nodeOpt
      no match {
        case None() => repr == List()
        case Some(node) => repr.head == node && validFrom(node.nextOpt, repr.tail)
      }
    }

    def valid: Boolean = {
      reads(repr.content ++ Set(this))
      validFrom(root, repr)
    }
  }

  case class Node(var nextOpt: Option[Node]) extends AnyHeapRef

  // @ghost def f(l: Node): Boolean = {
  //   reads(l.repr.content ++ Set(l))
  //   l.valid
  // }

  // def readInvariant(l1: Node, l2: Node): Unit = {
  //   reads(l1.repr.content ++ l2.repr.content)
  //   modifies(Set(l2))
  //   require(l1.valid && l2.valid && (l1.repr.content & l2.repr.content).isEmpty)
  //   val h1 = l1.value
  //   l2.value += 1
  //   val h2 = l1.value
  //   assert(h1 == h2)
  // }
}
