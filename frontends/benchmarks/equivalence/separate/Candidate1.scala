import defs._

object Candidate1 {
  def separate(xs: List[Animal]): (List[Sheep], List[Goat]) = {
    xs match {
      case Nil => (Nil, Nil)
      case (s: Sheep) :: t =>
        val (s2, g2) = separate(t)
        (s :: s2, g2)
      case (g: Goat) :: t =>
        val (s2, g2) = separate(t)
        (s2, g :: g2)
    }
  }
}