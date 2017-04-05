package withorb

import leon._
import lang._
import annotation._
import instrumentation._
import mem._
import higherorder._
import collection._
import invariant._

/**
 * Hint: requires unrollfactor=4
 */
object ZipWithAndFibStream {
  /**
   *  An infinite integer stream.
   *  Technically, the data structure is *not* infinite but the tail has a higher-order function.
   */
  case class SCons(x: BigInt, tailFun: ValOrSusp) {
    @inline
    def tail = tailFun match {
      case s@Susp(f) => s.fval
      case Val(x) => x
    }
    // this will not modify state
    @inline
    def tailVal = tailFun match {
      case s@Susp(f) => s.fval*
      case Val(x) => x
    }
    @inline
    def tailCached = tailFun match {
      case Val(_) => true
      case s => cached(s.fval)
    }
  }

  sealed abstract class ValOrSusp {
    // ideally, fval should not be called on `Val` as it would unnecessarily cache it.
    lazy val fval = {
      this match {
        case Susp(f) => f()
        case Val(x) => x
      }
    }
  }
  private case class Val(x: SCons) extends ValOrSusp
  private case class Susp(fun: () => SCons) extends ValOrSusp

  /**
   * A generic higher-order `zipWithFun` function.
   * The function is private so the targets of `f` are within scope.
   */
  private def zipWithFun(f: (BigInt, BigInt) => BigInt, xs: SCons, ys: SCons): SCons = {
    (xs, ys) match {
      case (SCons(x, _), SCons(y, _)) =>
        SCons(f(x, y), Susp(() => zipWithSusp(f, xs, ys)))
    }
  } ensuring(steps <= ?) // Orb result: 17

  private def zipWithSusp(f: (BigInt, BigInt) => BigInt, xs: SCons, ys: SCons): SCons = {
    zipWithFun(f, xs.tail, ys.tail)
  }

  /**
   * Properties of `zipWithFun`. In fact, they are generalizable beyond `zipWithFun`.
   */
  /**
   * Given first three elements of a stream,  the thridElem.tailFun is a suspension of `zipWithSusp` applied over
   * first and second element.
   */
  def argChainingProp(s: SCons): Boolean = {
    val first = s
    val second = first.tailVal
    val third = second.tailVal
    third.tailFun match {
      case Susp(fun) =>
        fun fmatch[(BigInt, BigInt) => BigInt, SCons, SCons, Boolean] {
          case (f, xs, ys) if (fun.is(() => zipWithSusp(f, xs, ys))) =>
            (xs == first && ys == second)
          case _ => false
        }
      case _ => false
    }
  }

  // proof that argchaining is satisfiable.
//  def gen: SCons = {
//    val f = (x: BigInt, y: BigInt) => x + y
//    val xs = SCons(0, Val(SCons(1, Susp(() => gen))))
//    val ys = SCons(1, Susp(() => gen))
//    SCons(1, Susp(() => zipWithSusp(f, xs, ys)))
//  }
//  //The following function should be sat i.e, invalid. The model is given by `y`
//  def argChainingIsSat(): Boolean = {
//    val y = SCons(0, Val(SCons(1, Susp(() => gen))))
//    !argChainingProp(y)
//  } holds

  /**
   * States that `argChaining` property holds for every sub-stream until a limit `n`
   * (note: this method could generalized to a co-recursive function)
   */
  @invisibleBody
  def argChainedStreamProp(s: SCons, n: BigInt): Boolean = {
    require(n >= 0)
    argChainingProp(s) &&
    (if(n == 0) true
    else {
     argChainedStreamProp(s.tailVal, n - 1)
    })
  }

  @invisibleBody
  def argChainingIsTransitive(s: SCons, n: BigInt): Boolean = {
    require(n >= 0 && argChainingProp(s))
    (if(n == 0) true
    else argChainingIsTransitive(s.tailVal, n - 1)) && argChainedStreamProp(s, n)
  } holds

  /**
   * First two elements have been evaluated
   */
  @inline
  def firstThreeEval(first: SCons, second: SCons, third: SCons) = {
    first.tailVal == second && second.tailVal == third &&
        first.tailCached && second.tailCached
  }

  /**
   * Given three elements, computes the next element.
   */
  @invisibleBody
  def next(f: SCons, s: SCons, t: SCons): SCons = {
    require(firstThreeEval(f, s, t) && argChainingProp(f))
    t.tail
  } ensuring(_ => steps <= ?) // Orb result: steps <= 73

  /**
   * Given the first three elements, reading the nth element (s.t. n >= 4) from a
   * `argChainedStream` will take only linear time.
   */
  @invisibleBody
  def nthElemAfterThird(n: BigInt, f: SCons, s: SCons, t: SCons): BigInt = {
    require(n >= 3  && firstThreeEval(f, s, t) && argChainedStreamProp(f, n))
    next(f, s, t) match {
      case fourth@SCons(x, _) =>
        if (n == 3) x
        else
          nthElemAfterThird(n - 1, s, t, fourth)
    }
  } ensuring(_ => steps <= ? * n + ?) // Orb result: 84 * n - 167

  /**
   * Using a `zipWithFun` function to implement a fibonacci stream.
   */
  val fibstream: SCons = SCons(0, Val(SCons(1, Susp(() => genNext))))
  @invisibleBody
  val genNext = {
    val fibs = this.fibstream
    zipWithSusp(_ + _, fibs, fibs.tail)
  } ensuring(_ => steps <= ?)

  /**
   * Establishes that `fibstream` satisfies `argChainedStream` property.
   */
  @invisibleBody
  def fibStreamSatisfiesProp(n: BigInt): Boolean = {
    require(n >= 0)
    val fibs = fibstream
    argChainingIsTransitive(fibs, n) && argChainedStreamProp(fibs, n)
  } holds

  /**
   * `nth` fib in O(n) time.
   */
  def nthFib(n: BigInt) = {
    require(n >= 0 && fibStreamSatisfiesProp(n))
    val first = fibstream
    if(n == 0) first.x
    else{
      val second = first.tail
      if(n == 1) second.x
      else {
        val third = second.tail
        if(n == 2) third.x
        else nthElemAfterThird(n, first, second, third)
      }
    }
  } ensuring(_ => steps <= ? * n + ?) // Orb result: 84 * n + 6
}