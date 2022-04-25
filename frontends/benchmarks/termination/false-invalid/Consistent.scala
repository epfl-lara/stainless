object Consistent {

  def test(a: Int): Int = {
    val neverApplied = () => test(a)
    0
  }
}
