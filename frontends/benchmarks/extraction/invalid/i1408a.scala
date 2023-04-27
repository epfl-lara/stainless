object i1408a {
  def test(): Int = {
    val x = scala.Option(2)
    5
  } ensuring (_ == 5)
}