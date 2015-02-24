/* Copyright 2009-2014 EPFL, Lausanne */

object LiteralMaps {
  def test(): Map[Int, Int] = {
    Map(1 -> 2, 3 -> 4, (5, 6))
  }

  def test2(): (Int, Int) = {
    1 -> 2
  }

  def test3(): Map[Int, Int] = {
    Map[Int, Int]()
  }

  def test4(): Map[Int, Int] = {
    Map.empty[Int, Int]
  }

  def test5(): Map[Int, Int] = {
    Map.empty[Int, Int]
  }
}
