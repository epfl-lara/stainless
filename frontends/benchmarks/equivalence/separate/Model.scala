import stainless.lang._
import stainless.collection.{List => SList}
import defs._

object Model {
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

  def test: SList[List[Animal]] = SList(
    Goat(1) :: Sheep(2) :: Nil
  )
}