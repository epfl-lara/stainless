
import stainless.lang._
import stainless.collection._
import stainless.annotation._

object PartialFold {

//   @partialEval
//   def sum(xs: List[BigInt]): BigInt = {
//     require(xs.length == 3)

//     xs.foldLeft(BigInt(0)) { _ + _ }
//   }

//   def test1 = {
//     sum(List(1,2,3)) == BigInt(6)
//   }.holds

  sealed abstract class Tree[A] {
    def fold[B](node: (B, B) => B)(leaf: A => B): B = this match {
      case Node(left, right) => node(left.fold(node)(leaf), right.fold(node)(leaf))
      case Leaf(value) => leaf(value)
    }
  }
  final case class Node[A](left: Tree[A], right: Tree[A]) extends Tree[A]
  final case class Leaf[A](value: A) extends Tree[A]

  def tree(a: BigInt, b: BigInt, c: BigInt, d: BigInt, e: BigInt): Tree[BigInt] =
    Node(
      Node(
        Leaf(a),
        Leaf(b)
      ),
      Node(
        Leaf(c),
        Node(
          Leaf(d),
          Leaf(e)
        )
      )
    )

  def id[A](x: A): A = x

  @partialEval
  def test(a: BigInt, b: BigInt, c: BigInt, d: BigInt, e: BigInt) = {
    tree(a, b, c, d, e).fold[BigInt](_ + _)(id)
  } ensuring { _ == a + b + c + d + e }

}
