import stainless.lang.swap
import stainless.lang.Cell
import stainless.lang.decreases
import stainless.collection.*
import stainless.annotation.*

object MutableTreeWithCell:
  sealed trait Tree
  case class Node(l: Cell[Tree], r: Cell[Tree]) extends Tree
  case class Leaf(x: BigInt) extends Tree

  def mirror(t: Tree): Unit = 
    t match
      case Node(l, r) =>
        mirror(l.v)
        mirror(r.v)
        swap(l, r)
      case Leaf(_) => ()

  def main(): Unit = 
    val t = Node(Cell(Node(Cell(Leaf(1)), Cell(Leaf(2)))), Cell(Node(Cell(Leaf(3)), Cell(Leaf(4)))))
    mirror(t)
    assert(t == Node(Cell(Node(Cell(Leaf(4)), Cell(Leaf(3)))), Cell(Node(Cell(Leaf(2)), Cell(Leaf(1))))))
