object PatternTests {
  def matching(a: Int): String = a match {
    case 1 => "First"
    case 2 => "Second"
    case b if b < 5 => "Third"
//    case _ => "Rest"
  }

  def pairMatching(a: (Int, String)): String = a match {
    case (1, "a") => "b"
    case (2, "b") => "a"
    case (c, d) if c > 4 => d
    case _ => "Rest"
  }
}