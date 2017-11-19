/* From LMCS 2008, Jones and Bohr */

import stainless.lang._

object ChurchNum {

  def succ(m: (BigInt => BigInt) => BigInt => BigInt)(s: BigInt => BigInt)(z: BigInt) = {
    m(s)(s(z))
  }

  def id(x: BigInt): BigInt = x

  def two(f: ((BigInt => BigInt) => BigInt => BigInt) => (BigInt => BigInt) => BigInt => BigInt)
         (z: (BigInt => BigInt) => BigInt => BigInt) = {
    f(f(z))
  }

  def zero(f: BigInt => BigInt)(z: BigInt) = z

  def main: Unit = two(succ)(zero)(id)(0)
}
