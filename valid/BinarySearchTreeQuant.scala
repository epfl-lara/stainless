import leon.lang._
import leon.collection._

object BSTSimpler {
  sealed abstract class Tree
  case class Node(left: Tree, value: BigInt, right: Tree) extends Tree
  case class Leaf() extends Tree

  def content(tree: Tree): Set[BigInt] = tree match {
    case Leaf() => Set.empty[BigInt]
    case Node(l, v, r) => content(l) ++ Set(v) ++ content(r)
  }

  def isBST(tree: Tree) : Boolean = tree match {
    case Leaf() => true
    case Node(left, v, right) => {
      isBST(left) && isBST(right) &&
      forall((x:BigInt) => (content(left).contains(x) ==> x < v)) &&
      forall((x:BigInt) => (content(right).contains(x) ==> v < x))
    }
  }

  def emptySet(): Tree = Leaf()

  def insert(tree: Tree, value: BigInt): Node = {
    require(isBST(tree))
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
  } ensuring(res => isBST(res) && content(res) == content(tree) ++ Set(value))

  def createRoot(v: BigInt): Node = {
    Node(Leaf(), v, Leaf())
  } ensuring (content(_) == Set(v))
}
