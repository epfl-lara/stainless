import stainless.lang._

// An anonymous class inherits the `???` body.
object UnimplementedAnonymousClass {
  abstract class Shape {
    def area(k: BigInt): BigInt = {
      require(k >= 0)
      (??? : BigInt)
    }.ensuring(_ >= 0)
  }

  def test: BigInt = {
    val s = new Shape {}
    s.area(1)
  }.ensuring(_ >= 0)
}
