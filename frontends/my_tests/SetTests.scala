object SetTests {

  def setCreate() = {
    val s1 = Set(1,2,3,1)
    val s2 = Set[Int]()
  }

  def setUnion(s1: Set[Char], s2: Set[Char]) = s1 ++ s2

  def setIntersect(s1: Set[Char], s2: Set[Char]) = s1 & s2

  def setDifference(s1: Set[Char], s2: Set[Char]) = s1 -- s2

  def setSubsetOf(s1: Set[Char], s2: Set[Char]) = s1 subsetOf s2

  def setContains(s1: Set[Char], s2: Char) = s1 contains s2
}
