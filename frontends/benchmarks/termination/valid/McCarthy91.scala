
/*
This function terminates for all inputs, see
http://en.wikipedia.org/wiki/McCarthy_91_function
Verifiable in a jiffy
*/
package termination.usermeasure
import stainless.lang._
object McCarthy91 {
  def rank(n: BigInt): BigInt = {
    if(n <= 100)
      101 - n
    else
      BigInt(0)
  } ensuring(_ >= 0)

  def M(n: BigInt): BigInt = {
    decreases(rank(n))
    if (n > 100)
      n-10
    else
      M(M(n+11))
  } ensuring(res => res == (if (n <= 100) BigInt(91) else n - 10))
}
