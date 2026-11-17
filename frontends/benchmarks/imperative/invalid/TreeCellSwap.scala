import stainless.lang.*
import stainless.lang.StaticChecks.*
import stainless.annotation.*

object TreeCellSwap:
  sealed trait Tree:
    @ghost def size: BigInt
  case class Node(l: Cell[Tree], r: Cell[Tree], @ghost ssize: BigInt) extends Tree:
    require(ssize == l.v.size + r.v.size + 1 && ssize > 0)
    @ghost @inline def size: BigInt = this.ssize

  case class Leaf(x: BigInt, @ghost ssize: BigInt) extends Tree:
    require(ssize == 1 && ssize > 0)
    @ghost @inline def size: BigInt = this.ssize

  def swapChildren(t: Tree): Unit =
    t match
      case Node(l, r, _) => swap(l, r)
      case Leaf(_, _) => ()

  def main(): Unit =
    val t = Node(Cell(Leaf(1, BigInt(1))), Cell(Leaf(2, BigInt(1))), BigInt(3))
    swapChildren(t)
    t.l.v match
      case Leaf(x, _) => assert(x == 2)
      case _ => assert(false)
