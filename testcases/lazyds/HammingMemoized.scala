package withOrb

import leon._
import mem._
import lang._
import annotation._
import instrumentation._
import invariant._
import leon.math._

/**
 * A memoized version of the implementation of Hamming problem shown in
 * section 4.3 of Type-based allocation analysis for Co-recursion.
 */
object Hamming {
  sealed abstract class IList
  case class Cons(x: BigInt, tail: IList) extends IList {
    @ignore
    override def toString: String = {
      if(tail == Nil()) x.toString
      else x.toString + "," + tail.toString
    }
  }
  case class Nil() extends IList {
    @ignore
    override def toString = ""
  }

  case class Data(v: BigInt, i2: BigInt, i3: BigInt, i5: BigInt)

  @invstate
  @memoize
  def ham(n: BigInt): Data = {
    decreases(abs(n))
    require(n ==0 || (n > 0 && depsEval(n - 1)))
    if(n == BigInt(0)) Data(1, 0, 0, 0)
    else {
      val Data(x, i2, i3, i5) = ham(n-1)
      val a = ham(i2).v * 2
      val b = ham(i3).v * 3
      val c = ham(i5).v * 5
      val (v, ni, nj, nk) = threeWayMerge(a, b, c, i2, i3, i5)
      Data(v, ni, nj, nk)
    }
  } ensuring(res =>  res.i2 <= n && res.i3 <= n && res.i5 <= n &&
      res.i3 >= 0 && res.i5 >= 0 && res.i2 >= 0 &&
      depsLem(res.i2, n) && depsLem(res.i3, n) && depsLem(res.i5, n) && // instantiations
      steps <= ?)

  def depsEval(i: BigInt): Boolean = {
    require(i >= 0)
    cached(ham(i)) && (if (i <= 0) true else depsEval(i - 1))
  }

  @traceInduct
  def depsEvalMono(i: BigInt, st1: Set[Fun[Data]], st2: Set[Fun[Data]]) = {
    require(i >= 0)
    (st1.subsetOf(st2) && (depsEval(i) in st1)) ==> (depsEval(i) in st2)
  } holds

  @traceInduct
  def depsLem(x: BigInt, y: BigInt) = {
    require(x >= 0 && y >= 0)
    (x <= y && depsEval(y)) ==> depsEval(x)
  } holds

  def invoke(n: BigInt) = {
    require(n == 0 || n > 0 && depsEval(n - 1))
    ham(n).v
  } ensuring (res => {
    val in = inSt[Data]
    val out = outSt[Data]
    (n == 0 || depsEvalMono(n-1, in, out)) && // instantiation
      steps <= ?
  })

  /**
   * Returns a list of hamming numbers upto 'n'
   */
  def hammingList(n: BigInt): IList = {
    require(n >= 0)
    if(n == 0) {
        Cons(invoke(n), Nil())
    } else {
      val tailRes =  hammingList(n-1)
      Cons(invoke(n), tailRes)
    }
  } ensuring(_ => depsEval(n) && steps <= ? * n + ?)

  @inline
   def threeWayMerge(a: BigInt, b: BigInt, c: BigInt, i2: BigInt, i3: BigInt, i5: BigInt) = {
      if(a == b && b == c)      (a, i2 + 1, i3 + 1, i5 + 1)
      else if(a == b && a < c)  (a, i2 + 1, i3 + 1, i5    )
      else if(a == c && a < b)  (a, i2 + 1, i3    , i5 + 1)
      else if(b == c && b < a)  (b, i2    , i3 + 1, i5 + 1)
      else if(a < b && a < c)   (a, i2 + 1, i3    , i5    )
      else if(b < c && b < a)   (b, i2    , i3 + 1, i5    )
      else/*if(c < a && c < b)*/(c, i2    , i3    , i5 + 1)
   }

  @ignore
  def main(args: Array[String]) {
    import collection._
    val hlist = hammingList(100) // without memoization this will take too long
    println("Hamming numbers: "+hlist)
  }
}
