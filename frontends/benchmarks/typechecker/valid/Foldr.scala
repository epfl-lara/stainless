/* From Sereni, PhD thesis 2006 */

import stainless.lang._
import stainless.collection._

object Foldr {

  def foldr[A,Z](list: List[A])(z: Z)(f: (A,Z) => Z): Z = {
    decreases(list)
    list match {
      case Cons(x, xs) => f(x, foldr(xs)(z)(f))
      case Nil() => z
    }
  }

  def sum(m: BigInt, n: BigInt) = m + n

  def main(list: List[BigInt]) = foldr(list)(BigInt(0))(sum)
}
