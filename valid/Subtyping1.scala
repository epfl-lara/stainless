/* Copyright 2009-2014 EPFL, Lausanne */

object Subtyping1 {

  sealed abstract class Tree
  case class Leaf() extends Tree
  case class Node(left: Tree, value: Int, right: Tree) extends Tree

  def content(t: Tree) : Set[Int] = t match {
    case Leaf() => Set.empty
    case Node(l, v, r) => content(l) ++ Set(v) ++ content(r)
  }

  def treeMax(tree: Node): Int = {
    tree match {
      case Node(_, v, right) => right match {
        case Leaf() => v
        case Node(l, v, r) => treeMax(Node(l, v, r))
      }
    }
  } ensuring(content(tree).contains(_))

  def f2(tree: Node): Int = {
    require(treeMax(tree) > 0)
    tree match {
      case Node(_, v, right) => right match {
        case Leaf() => v
        case Node(l, v, r) => treeMax(Node(l, v, r))
      }
    }
  } ensuring(content(tree).contains(_))

}
