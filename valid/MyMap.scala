/* Copyright 2009-2013 EPFL, Lausanne */

import leon.Utils._

object MyMap {

  def map1(): Int = {
    val m = Map(1 -> 2, 2 -> 3, 3 -> 4)
    m(2)
  } ensuring(_ == 3)

  def map2(): Boolean = {
    val m1 = Map[Int, Int]()
    val m2 = Map.empty[Int, Int]
    m1 == m2
  }.holds

}
