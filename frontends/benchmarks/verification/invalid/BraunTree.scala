/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object BraunTree {
  sealed abstract class Tree
  case class Node(value: Int, left: Tree, right: Tree) extends Tree
  case class Leaf() extends Tree

  def insert(tree: Tree, x: Int): Tree = {
    require(isBraun(tree))
    tree match {
      case Node(value, left, right) =>
        Node(value, insert(left, x), right)
      case Leaf() => Node(x, Leaf(), Leaf())
    }
  } ensuring { res => isBraun(res) }

  def height(tree: Tree): Int = {
    tree match {
      case Node(value, left, right) =>
        val l = height(left)
        val r = height(right)
        val max = if (l > r) l else r
        1 + max
      case Leaf() => 0
    }
  }

  def isBraun(tree: Tree): Boolean = {
    tree match {
      case Node(value, left, right) =>
        isBraun(left) && isBraun(right) && {
          val l = height(left)
          val r = height(right)
          l == r || l == r + 1
        }
      case Leaf() => true
    }
  }
}
