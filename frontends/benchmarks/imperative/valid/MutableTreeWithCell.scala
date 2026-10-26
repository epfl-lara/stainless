import stainless.collection.*
import stainless.annotation.*
import stainless.lang.StaticChecks.*
import stainless.lang.old
import stainless.lang.*
import stainless.proof.*

object MutableTreeWithCell:
  sealed trait Tree:
    @ghost def size: BigInt
  case class Node(l: Cell[Tree], r: Cell[Tree], @ghost ssize: BigInt) extends Tree:
    require(ssize == l.v.size + r.v.size + 1 && ssize > 0)
    @ghost @inline def size: BigInt = this.ssize

  case class Leaf(x: BigInt, @ghost ssize: BigInt) extends Tree:
    require(ssize == 1 && ssize > 0)
    @ghost @inline def size: BigInt = this.ssize


  def mirror(t: Tree): Unit = 
    decreases(t.size)
    t match
      case Node(l, r, _) =>
        mirror(l.v)
        mirror(r.v)
        swap(l, r)
      case Leaf(_, _) => ()

  def main(): Unit = 
    val t = Node(
              Cell(Node(
                  Cell(Leaf(4, BigInt(1))), 
                  Cell(Leaf(3, BigInt(1))), BigInt(3))), 
              Cell(Node(
                  Cell(Leaf(2, BigInt(1))), 
                  Cell(Leaf(1, BigInt(1))), BigInt(3))), BigInt(7))
    mirror(t)
