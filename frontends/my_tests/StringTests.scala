object StringTests {

  def makeString() = {
    val first = "first"
    "second"
  }

  def stringLength(s: String) = {
    s.length
  }

  def stringConcat(s1: String, s2: String) = {
    s1 + s2
  }

  def stringSubString(s2: String, a: BigInt, b: BigInt) = {
    s2.substring(a, b)
  }
}
