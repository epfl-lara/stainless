import stainless.lang._
import stainless.collection._

object i1408c {
  def myBigTest(s: Set[BigInt]): Int = {
    {
      val x = scala.Option(2)
      s
    } ++ s
    5
  }
}