object MapTests {

  def mapCreate(): Unit = {
    val m1 = Map[Int, Int]().withDefault(3)
    val m2 = Map[Int, Char]((1, '1'), (3, '2')).withDefault('b')
  }

  def mapGet(map: Map[Int, Char]) = map.get(1)

  def mapUpdate(map: Map[Int, Char], from: Int, to: Char) = map + (from -> to)
}
