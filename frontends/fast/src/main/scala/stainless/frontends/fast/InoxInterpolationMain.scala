package stainless.frontends.fast

import inox._
import inox.trees._
import inox.trees.interpolator._

object InoxInterpolationMain {
  implicit val mySymbols = NoSymbols


  def main(args: Array[String]): Unit = {
    val Seq(listSort, sizeFunDef) = p"""

      def size[A, B](a: A, b: B): (A, B) = (a, b)

      def main(): (Int, Int) = {
        size(1, 2)
      }
    """
    print(listSort)
    print(sizeFunDef)
  }
}
