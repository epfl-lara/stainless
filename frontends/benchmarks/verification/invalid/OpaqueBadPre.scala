import stainless.annotation._

object OpaqueBadPre {

  @opaque
  def f(x: BigInt): BigInt = {
    require(x >= 0)
    -x
  }

  def test(): Unit = {
    f(-100)
  }
}
