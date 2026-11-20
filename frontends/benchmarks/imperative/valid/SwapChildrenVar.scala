import stainless.annotation.*
import stainless.lang.StaticChecks.*
import stainless.lang.*

object SwapChildrenVar:
  sealed trait Tree
  case class Node(var l: Tree, var r: Tree) extends Tree
  case class Leaf(x: BigInt) extends Tree

  def swapChildren(t: Tree): Unit =
    t match
      case n @ Node(_, _) =>
        val tmp = n.l
        n.l = n.r
        n.r = tmp
      case Leaf(_) => ()

  def main(): Unit =
    val t = Node(Node(Leaf(4), Leaf(3)), Leaf(1))
    swapChildren(t)
    t.l match
      case Leaf(x) => assert(x == 1)
      case _ => assert(false)
    t.r match
      case Node(Leaf(y), _) => assert(y == 4)
      case _ => assert(false)
