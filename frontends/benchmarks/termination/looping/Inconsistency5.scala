object Inconsistency5 {
  case class Machine(f: Any => Boolean)

  def negateDiagonal(x: Any): Boolean = 
    if (x.isInstanceOf[Machine])
      !x.asInstanceOf[Machine].f(x)
    else
      true

  def theorem() = {
    val m = Machine(negateDiagonal _)
    negateDiagonal(m) // reduces to !negateDiagonal(m)
  }
}
