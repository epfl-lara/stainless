import stainless.lang._
import stainless.annotation._
import stainless.collection._
import stainless.proof._

object NodeCycleExample {
  /* Auxiliary definitions and lemmas */

  def allDifferent[T](xs: List[T]): Boolean =
    xs match {
      case Nil() => true
      case Cons(x, xs0) => !xs0.content.contains(x) && allDifferent(xs0)
    }

  object ListLemmas {
    def lastByIndex[T](xs: List[T]): Unit = {
      require(xs.nonEmpty)
      xs.tail match {
        case Nil() => ()
        case xs0 => lastByIndex(xs0)
      }
    } ensuring (_ => xs(xs.size - 1) == xs.last)

    def initByIndex[T](xs: List[T], i: BigInt): Unit = {
      require(xs.nonEmpty && 0 <= i && i < xs.size - 1)
      if (i > 0) initByIndex(xs.tail, i - 1)
    } ensuring (_ => xs(i) == xs.init(i))

    def applyContent[T](xs: List[T], i: BigInt): Unit = {
      require(0 <= i && i < xs.size)
      xs match {
        case Cons(_, xs0) => if (i > 0) applyContent[T](xs0, i - 1)
      }
    } ensuring (_ => xs.content.contains(xs.apply(i)))

    @extern
    def allDifferentLast[T](xs: List[T]): Unit = {
      require(xs.nonEmpty && allDifferent(xs))
      ()
    } ensuring (_ => !xs.init.content.contains(xs.last))
  }

  /* Node data structure and cyclicity property */

  case class Node(var next: Option[Node]) extends AnyHeapRef

  def cyclic(nodes: List[Node], i: BigInt = 0): Boolean = {
    reads(nodes.content.asRefs)
    require(0 <= i && i < nodes.size)
    ListLemmas.applyContent(nodes, i)
    if (i == nodes.size - 1)
      nodes(i).next == Some(nodes(0))
    else
      nodes(i).next == Some(nodes(i + 1)) && cyclic(nodes, i + 1)
  }

  /* Lemma: Prepending maintains cyclicity */

  def cyclicPrependLemma(h0: Heap, h1: Heap, nodes: List[Node], node: Node, i: BigInt = 0): Unit = {
    require(
      0 <= i && i < nodes.size &&
      h0.eval { cyclic(nodes, i) } &&
      Heap.unchanged(nodes.init.content.asRefs, h0, h1) &&
      h1.eval { nodes.last.next == Some(node) }
    )
    if (i == nodes.size - 1) {
      ListLemmas.lastByIndex(nodes)           // nodes(nodes.size - 1) == nodes.last
    } else {
      ListLemmas.initByIndex(nodes, i)        // nodes(i) == nodes.init(i)
      ListLemmas.applyContent(nodes.init, i)  // nodes.init.content.contains(nodes.init(i))
      assert(h1.eval { nodes(i).next == Some(nodes(i + 1)) })
      cyclicPrependLemma(h0, h1, nodes, node, i + 1)
    }
  } ensuring (_ => h1.eval { cyclic(node :: nodes, i + 1) })

  def prepend(nodes: List[Node], node: Node): List[Node] = {
    reads(nodes.content.asRefs ++ Set(node))
    modifies(nodes.content.asRefs ++ Set(node))
    require(nodes.nonEmpty && cyclic(nodes) && allDifferent(nodes) && !nodes.content.contains(node))
    val h0 = Heap.get

    node.next = Some(nodes.head)
    nodes.last.next = Some(node)

    val h1 = Heap.get
    ListLemmas.allDifferentLast(nodes)  // Heap.unchanged(nodes.init.content.asRefs, h0, h1)
    cyclicPrependLemma(h0, h1, nodes, node)
    node :: nodes
  } ensuring (newNodes => newNodes == node :: nodes && cyclic(newNodes) && allDifferent(newNodes))
}
