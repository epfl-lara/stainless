/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._

object MyMap {

  def map1(): Int = {
    val m = Map(1 -> 2, 2 -> 3, 3 -> 4)
    m(2)
  } ensuring(_ == 3)

  def map2() = {
    val m1 = Map(1 -> 2)
    assert(!m1.contains(2))
    val m2 = m1.updated(2, 3)
    assert(m2.contains(2))
    assert(m2(2) == 3)
    val m3 = m2.removed(2)
    assert(!m3.contains(2))
    assert(m3.contains(1))
    assert(m3(1) == 2)
  }

  def map3(): Boolean = {
    val m1 = Map[Int, Int]()
    val m2 = Map.empty[Int, Int]
    m1 == m2
  }.holds

}
