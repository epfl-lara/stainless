import stainless.lang._
object SelfTypeMemberClasses {
  trait Exprs { self: Trees =>
    case class Lit(v: BigInt) {
      def doubled: BigInt = scale * v
      def tree: Tree = Leaf(v)
    }
  }
  trait Trees extends Exprs {
    case class Leaf(v: BigInt) extends Tree
    abstract class Tree
    def scale: BigInt = 2
  }
  case object trees extends Trees
  def test: Unit = { assert(trees.Lit(3).doubled == 6) }
}
