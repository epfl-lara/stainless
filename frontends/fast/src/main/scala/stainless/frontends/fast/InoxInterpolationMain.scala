package stainless.frontends.fast

import inox._
import inox.trees._
import inox.trees.interpolator._

object InoxInterpolationMain {
  implicit val mySymbols = NoSymbols


  def main(args: Array[String]): Unit = {
    val Seq(listSort, sizeFunDef) = p"""

      def size(xs: List): Int =
        if (xs is Cons)
          0
        else
          xs.head

      type List = Cons(head: Int, tail: List) | Nil()
    """
    listSort
  }
}
