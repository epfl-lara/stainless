package termination
package usermeasure.higherorder

import stainless._
import lang._
import annotation._
import collection._

object CFATest {

  def test1(f: (Unit => BigInt) => BigInt, xs: BigInt): BigInt = {
    val l = (u: Unit) => xs
    f(l)
  }

  def test2(): BigInt = {
    val f = (l: Unit => BigInt) => l()
    test1(f, BigInt(0))
  }
}