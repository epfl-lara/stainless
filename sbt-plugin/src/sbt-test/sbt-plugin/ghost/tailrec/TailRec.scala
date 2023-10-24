package test

import stainless._
import stainless.annotation.{ghost => ghostAnnot, _}
import stainless.lang._
import StaticChecks._

object Main {
  import stainless.lang.WhileDecorations

  def loop1(count: Long, l1: Long, l2: Long, l3: Long): Long = {
    require(count >= 0)
    decreases(count)
    if (count == 0) l1
    else loop1(count - 1, l1, l2, l3)
  }.ensuring(_ == l1)

  def loop2(count: Long, l1: Long, l2: Long, l3: Long): Long = {
    require(count >= 0)
    decreases(count)
    if (count == 0) l1
    else {
      val myRes = loop2(count - 1, l1, l2, l3)
      ghost {
        assert(myRes == l1)
      }
      myRes
    }
  }.ensuring(_ == l1)

  def whileLoop(upto: Long): Unit = {
    var i: Long = 0
    (while(i < upto) {
      decreases(upto - i)
      i += 1
    }).invariant(i >= 0)
  }

  def main(args: Array[String]): Unit = {
    loop1(100000, 1, 2, 3)
    loop2(100000, 1, 2, 3)
    whileLoop(10000)
  }
}
