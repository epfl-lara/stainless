import stainless.lang.StaticChecks._

object i1408b {
  def test(): Int = {
    5
  }.ensuring(_ == {
    val x = scala.Option(2)
    5
  })
}
