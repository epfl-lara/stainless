import stainless.lang._
import stainless.collection._

case class Alphabet(i: BigInt)

object Alphabet {
  def values: List[Alphabet] = choose((res: List[Alphabet]) => true)
}

object LazyTree {

  sealed abstract class Tree[T] {
    def depth: BigInt

    def lookup(word: List[T]): Boolean = (this, word) match {
      case (Node(child, _), Cons(x, xs)) => child(x).lookup(xs)
      case (_, Nil()) => true
      case _ => false
    }
  }

  case class Node[T](child: T => Tree[T], depth: BigInt) extends Tree[T] {
    require(depth > 0 && forall((t: T) => child(t).depth < depth))
  }

  case class Leaf[T]() extends Tree[T] {
    val depth: BigInt = 0
  }

  def fold[C](tree: Tree[Alphabet], f: List[C] => C): C = {
    decreases(tree.depth)
    tree match {
      case Node(child, _) => f(Alphabet.values.map(a => fold(child(a), f)))
      case Leaf() => f(Nil())
    }
  }
}
