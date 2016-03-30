import leon.lang._
import leon.collection._

object BSTSimpler2 {

  sealed abstract class Tree {
    def content: Set[BigInt] = this match {
      case Leaf() => Set.empty[BigInt]
      case Node(l, v, r) => l.content ++ Set(v) ++ r.content
    }
  }

  case class Node(left: Tree, value: BigInt, right: Tree) extends Tree {
    require(forall((x:BigInt) => (left.content.contains(x) ==> x < value)) &&
      forall((x:BigInt) => (right.content.contains(x) ==> value < x)))
  }

  case class Leaf() extends Tree

  def emptySet(): Tree = Leaf()

  def insert(tree: Tree, value: BigInt): Node = {
    tree match {
      case Leaf() => Node(Leaf(), value, Leaf())
      case Node(l, v, r) => (if (v < value) {
        Node(l, v, insert(r, value))
      } else if (v > value) {
        Node(insert(l, value), v, r)
      } else {
        Node(l, v, r)
      })
    }
  } ensuring(res => res.content == tree.content ++ Set(value))

}
