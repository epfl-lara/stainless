import stainless.annotation.*
import stainless.lang.StaticChecks.*
import stainless.lang.*

object MirrorSpecWrong:
  sealed trait Tree
  case class Node(var l: Tree, var r: Tree) extends Tree
  case class Leaf(x: BigInt) extends Tree

  def leftmost(t: Tree): BigInt = t match
    case Node(l, _) => leftmost(l)
    case Leaf(x) => x

  def rightmost(t: Tree): BigInt = t match
    case Node(_, r) => rightmost(r)
    case Leaf(x) => x

  def mirror(t: Tree): Unit = {
    t match
      case n @ Node(_, _) =>
        mirror(n.l)
        mirror(n.r)
        val tmp = n.l
        n.l = n.r
        n.r = tmp
      case Leaf(_) => ()
  }.ensuring(_ => leftmost(t) == rightmost(old(t)))

  def main(): Unit =
    val t = Node(Node(Leaf(4), Leaf(3)), Node(Leaf(2), Leaf(1)))
    mirror(t)
    assert(leftmost(t) == 4)
