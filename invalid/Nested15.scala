/* Copyright 2009-2015 EPFL, Lausanne */
import leon.collection._
object Nested15 {

  def foo[A](i: List[A]): BigInt = {
    val n = i
    def rec1[B](j: List[B]) = j ++ j
    def rec2[C](l: List[C], j: BigInt) = {
      require(l.nonEmpty)
      def rec3(k: C) = k :: rec1[C](l)
      rec3(l.head).size + j + n.size + i.size
    }
    rec2(List(true, true, false), 2)
  } ensuring(_ == i.size + 9) // Should be 2* size

}

