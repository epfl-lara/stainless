object Inconsistency5 {
  case class Machine(f: Any => Boolean)

  def negateDiagonal(x: Any): Boolean =
    if (x.isInstanceOf[Machine]) {
      val m = x.asInstanceOf[Machine]
      !m.f(m)
    } else true

  def theorem() = {
    val m = Machine(negateDiagonal _)
    negateDiagonal(m) // reduces to !negateDiagonal(m)
  }
}
