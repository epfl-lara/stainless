import stainless.lang._

object ImmutableOld {
  case class Test(i: BigInt)
  def test(t: Test): BigInt = {
    t.i
 }.ensuring(_ == old(t).i)
}
