/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._

object MySet {

  def set1(): Boolean = {
    val s = Set(1, 2, 3, 4)
    s.contains(3)
  }.holds

  def set2(): Boolean = {
    val s1 = Set[Int]()
    val s2 = Set.empty[Int]
    s1 == s2
  }.holds

}
