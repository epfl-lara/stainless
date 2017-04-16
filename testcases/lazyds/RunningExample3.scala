package withOrb

import leon._
import mem._
import higherorder._
import lang._
import annotation._
import instrumentation._
import invariant._
import collection._

/**
 * The running examples used in the paper
 */
object RunningExample {

  sealed abstract class Bool
  case class True() extends Bool
  case class False() extends Bool

  sealed abstract class Stream
  private case class SCons(x: BigInt, tailFun: () => Stream) extends Stream {
    lazy val tail = tailFun()
  }
  private case class SNil() extends Stream

  private val primeStream = {
    SCons(1, () => nextElem(BigInt(2)))
  }

  /*def isPrimeRec(i: BigInt, n: BigInt): Bool = {
    require(i >= 1 && i < n)
    if(i == 1) True()
    else if((n / i) * i == n) False()
    else isPrimeRec(i - 1, n)
  } ensuring(_ => steps <= ? * i + ?)*/

  def isPrimeNum(n: BigInt): Bool = {
    require(n >= 2)
    def rec(i: BigInt): Bool = {
      require(i >= 1 && i < n)
      if (i == 1) True()
      else if ((n / i) * i == n) False()
      else rec(i - 1)
    } ensuring (_ => steps <= ? * i + ?)
    rec(n -1)
  } //ensuring(r => steps <= ? * n + ?)

  def nextElem(i: BigInt): Stream = {
    require(i >= 2)
    if(isPrimeNum(i) == True()){
      SCons(i, () => nextElem(i+1))
    } else
      nextElem(i+1)
  }

  def isPrimeS(s: Stream): Boolean = {
   s match {
     case SNil() => true
     case SCons(x, tfun) =>
       x >= 2 && (isPrimeNum(x) == True()) && isPrimeS(tfun())
   }}

 def takeRec(i: BigInt, n: BigInt, s: Stream): Stream = {
  require(0 <= i && i <= n && isPrimeS(s))
  s match {
   case c@SCons(x, _) =>
     if(i < n) {
       val j = i + 1
       val ct = c.tail
       SCons(x, () => takeRec(j, n, ct))
     }
     else SNil()
   case _ => SNil()
  }
 } ensuring{r => isPrimeS(r)}
}
