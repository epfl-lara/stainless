package withOrb

import leon._
import mem._
import lang._
import annotation._
import instrumentation._
import invariant._

object FibMem {
  sealed abstract class IList
  case class Cons(x: BigInt, tail: IList) extends IList
  case class Nil() extends IList

  @memoize
  def fibRec(n: BigInt): BigInt = {
    require(n >= 0)
    if (n <= 2)
      BigInt(1)
    else
      fibRec(n - 1) + fibRec(n - 2) // postcondition implies that the second call would be cached
  } ensuring (_ =>
    (n <= 2 || (cached(fibRec(n - 1)) &&
      cached(fibRec(n - 2)))) && steps <= ? * n + ?)

  @ignore
  def main(args: Array[String]) {
    println("32nd fibonnacci number: " + fibRec(50))
  }
}
