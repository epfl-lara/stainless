object PatternAlternative2 {
  sealed trait Tree
  case class Node(left: Tree, right: Tree) extends Tree
  case class IntLeaf(value: Int) extends Tree
  case class StringLeaf(value: String) extends Tree
  case class NoneLeaf() extends Tree

  def containsNoneLeaf(tree: Tree): Boolean = {
    tree match {
      case Node(left, right) => containsNoneLeaf(left) || containsNoneLeaf(right)
      case NoneLeaf() => true
      case _ => false
    }
  }

  def containsOnlyBinaryLeaves(tree: Tree): Boolean = {
    tree match {
      case Node(left, right) => containsOnlyBinaryLeaves(left) && containsOnlyBinaryLeaves(right)
      case IntLeaf(v) => v == 0 || v == 1
      case StringLeaf(v) => v == "0" || v == "1"
      case _ => true
    }
  }

  def hasBinaryLeaves(tree: Tree): Boolean = {
    require(!containsNoneLeaf(tree) && containsOnlyBinaryLeaves(tree))
    tree match {
      case a @ Node(left: (IntLeaf | StringLeaf), right: (IntLeaf | StringLeaf)) => hasBinaryLeaves(left) && hasBinaryLeaves(right)
      case b @ (IntLeaf(0 | 1) | StringLeaf("0" | "1")) => true
      case _ => false
    }
  } ensuring { res => res }
}