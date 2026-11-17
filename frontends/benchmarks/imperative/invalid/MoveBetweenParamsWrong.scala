import stainless.annotation.*
import stainless.lang.StaticChecks.*
import stainless.lang.*

object MoveBetweenParamsWrong:
  sealed trait Tree
  case class Node(var l: Tree, var r: Tree) extends Tree
  case class Leaf(x: BigInt) extends Tree

  def move(a: Node, b: Node, k: BigInt): Unit =
    if k > 0 then move(a, b, k - 1)
    else
      b.l = a.l
      a.l = Leaf(0)

  def main(): Unit =
    val a = Node(Leaf(7), Leaf(8))
    val b = Node(Leaf(5), Leaf(6))
    move(a, b, 2)
    b.l match
      case Leaf(x) => assert(x == 5)
      case _ => assert(false)
    a.l match
      case Leaf(y) => assert(y == 0)
      case _ => assert(false)
