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
 * Hint: requires unrollfactor=4, and vcTimeout=35
 * Implementation obtained from ESOP 2015 paper type-based allocation analysis for co-recursion.
 */
object MergeAndHammingNumbers {
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
   * A generic lazy higher-order `map` function
   */
  @invisibleBody
  private def map(f: BigInt => BigInt, xs: SCons): SCons = {
    xs match {
      case SCons(x, _) =>
        SCons(f(x), Susp(() => mapSusp(f, xs)))
    }
  } ensuring(steps <= ?) // Orb result: 11

  private def mapSusp(f: BigInt => BigInt, xs: SCons): SCons = {
    map(f, xs.tail)
  }

  def min(x: BigInt, y: BigInt, z: BigInt) = {
    if(x <= y)
      if(x <= z) x else z
    else
      if(y <= z) y else z
  }

  /**
   * A three way merge function
   */
  @invisibleBody
  def merge(a: SCons, b: SCons, c: SCons): SCons = {
    val susp = Susp(() => mergeSusp(a, b, c))
    SCons(min(a.x, b.x, c.x), susp)
  } ensuring (_ => steps <= ?)  // Orb result: 11

  @invisibleBody
  def force(a: SCons) = {
    a.tail
  } ensuring{_ =>
    val in = inSt[BigInt]
    if((constTimeArg(a) in in))
      steps <= ? // Orb result: 223
    else true
  }

  @invisibleBody
  def mergeSusp(a: SCons, b: SCons, c: SCons): SCons = {
    val m = min(a.x, b.x, c.x)
    val nexta = if (a.x == m) force(a) else a //.tail
    val nextb = if (b.x == m) force(b) else b
    val nextc = if (c.x == m) force(c) else c
    merge(nexta, nextb, nextc)
  } ensuring{_ =>
    val in = inSt[BigInt]
    if((constTimeArg(a) in in) && (constTimeArg(b) in in)
        && (constTimeArg(c) in in))
      steps <= ? // Orb result: 223
    else true
  }

  def constTimeArg(a: SCons): Boolean = {
    a.tailFun match {
      case Susp(fun) =>
        fun fmatch[BigInt => BigInt, SCons, Boolean] {
          case (f, xs) if fun.is(() => mapSusp(f, xs)) => xs.tailCached
          case _ => false
        }
      case _ => false
    }
  }

  /**
   * Given the first element of a stream, first.tailFun is a suspension of `map` applied over
   * first element.
   */
  def mergeUsesMap(first: SCons, mergeArg: SCons): Boolean = {
    mergeArg.tailFun match {
      case Susp(fun) =>
        fun fmatch[BigInt => BigInt, SCons, Boolean] {
          case (f, xs) if fun.is(() => mapSusp(f, xs)) => xs == first
          case _ => false
        }
      case _ => false
    }
  }

  def mergeMapProp(s: SCons): Boolean = {
    val first = s
    val second = first.tailVal
    second.tailFun match {
      case Susp(fun) =>
        fun fmatch[SCons, SCons, SCons, Boolean] {
          case (a, b, c) if fun.is(() => mergeSusp(a, b, c)) =>
            mergeUsesMap(first, a) && mergeUsesMap(first, b)  && mergeUsesMap(first, c)
          case _ => false
        }
      case _ => false
    }
  } //ensuring(res => !res) enable this to know that the property is satisfiable

  /**
   * States that `argChaining` property holds for every sub-stream until a limit `n`
   * (note: this method could generalized to a co-recursive function)
   */
  @invisibleBody
  def argChainedStreamProp(s: SCons, n: BigInt): Boolean = {
    require(n >= 0)
    mergeMapProp(s) &&
    (if(n == 0) true
    else {
     argChainedStreamProp(s.tailVal, n - 1)
    })
  }

  @invisibleBody
  def argChainingIsTransitive(s: SCons, n: BigInt): Boolean = {
    require(n >= 0 && mergeMapProp(s))
    (if(n == 0) true
    else argChainingIsTransitive(s.tailVal, n - 1)) && argChainedStreamProp(s, n)
  } holds

  /**
   * Given two elements, computes the next element.
   */
  @invisibleBody
  def next(f: SCons, s: SCons): SCons = {
    require(f.tailVal == s && f.tailCached && mergeMapProp(f))
    s.tail
  } ensuring(_ => steps <= ?) // Orb result: steps <= 250

  /**
   * Given the first three elements, reading the nth element (s.t. n >= 4) from a
   * `argChainedStream` will take only linear time.
   */
  @invisibleBody
  def nthElemAfterSecond(n: BigInt, f: SCons, s: SCons): BigInt = {
    require(n >= 2  && f.tailVal == s && f.tailCached && argChainedStreamProp(f, n))
    next(f, s) match {
      case t@SCons(x, _) =>
        if (n == 2) x
        else
          nthElemAfterSecond(n - 1, s, t)
    }
  } ensuring(_ => steps <= ? * n + ?) // Orb result: 261 * n - 260

   /**
   * A stream generating hamming numbers
   */
  val hamstream: SCons = SCons(1, Susp(() => hamGen))
  @invisibleBody
  def hamGen = {
    val hs = this.hamstream
    merge(map(2 * _, hs), map(3 * _, hs), map(5 * _, hs))
  } ensuring(_ => steps <= ?) // Orb result: 63

  @invisibleBody
  def hamStreamSatisfiesProp(n: BigInt): Boolean = {
    require(n >= 0)
    val s = hamstream
    argChainingIsTransitive(s, n) && argChainedStreamProp(s, n)
  } holds

  /**
   * `nth` hamming number in O(n) time.
   */
  def nthHammingNumber(n: BigInt) = {
    require(n >= 0 && hamStreamSatisfiesProp(n))
    val first = hamstream
    if(n == 0) first.x
    else{
      val second = first.tail
      if(n == 1) second.x
      else nthElemAfterSecond(n, first, second)
    }
  } ensuring(_ => steps <= ? * n + ?) // Orb result: 84 * n + 6
}