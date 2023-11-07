object i1474 {
  import stainless.lang._
  import stainless.lang.StaticChecks._
  import stainless.annotation._

  @mutable
  sealed abstract class Opt[@mutable T]
  case class NONE[@mutable T]() extends Opt[T]
  case class SOME[@mutable T](value: T) extends Opt[T]

  final case class Node(var head: Int, var next: Cell[Opt[Node]])

  @extern
  def getLast(n: Node): Node = {
    n.next.v match {
      case NONE() => n
      case SOME(next) => getLast(next)
    }
  }

  final case class TList(var first: Node,
                         var last: Node) {
    require(last == getLast(first))
  }

  def mkEnd(head: Int): Node = Node(head, Cell(NONE[Node]()))

  def test = {
    val n1: Node = mkEnd(5)
    val l: TList = TList(n1, freshCopy(n1))
  }
}