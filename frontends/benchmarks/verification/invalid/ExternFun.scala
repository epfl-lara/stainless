
import stainless.lang._
import stainless.annotation._

object ExternFun {

  @extern
  def stuff(x: BigInt): BigInt = x

  def test(n: BigInt) = {
    stuff(n) == n
  }.holds

}
