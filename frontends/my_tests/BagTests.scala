object BagTests {

  def bagCreate() = {
    val s1 = Bag((1, BigInt(2)), (3, BigInt(1)), (4, BigInt(3)))
    val s2 = Bag[Int]()
    val a = BigInt(4)
  }

  def bagUnion(s1: Bag[Char], s2: Bag[Char]) = s1 ++ s2

  def bagIntersect(s1: Bag[Char], s2: Bag[Char]) = s1 & s2

  def bagDifference(s1: Bag[Char], s2: Bag[Char]) = s1 -- s2

  def bagContains(s1: Bag[Char], s2: Char) = s1 contains s2
}
