package orb

import leon._
import mem._
import lang._
import annotation._
import instrumentation._
import invariant._

object WeightedSched {
  sealed abstract class IList {
    def size: BigInt = {
      this match {
        case Cons(_, tail) => 1 + tail.size
        case Nil()         => BigInt(0)
      }
    } ensuring (_ >= 0)
  }
  case class Cons(x: BigInt, tail: IList) extends IList
  case class Nil() extends IList

  /**
   * array of jobs
   * (a) each job has a start time, finish time, and weight
   * (b) Jobs are sorted in ascending order of finish times
   * The first job should be (0,0,0) so that it acts as sentinel of every other job
   */
  @ignore
  var jobs = Array[(BigInt, BigInt, BigInt)]()

  /**
   * A precomputed mapping from each job i to the previous job j it is compatible with.
   * The value of the first index could be anything.
   */
  @ignore
  var p = Array[Int]()

  @extern
  def jobInfo(i: BigInt) = {
    jobs(i.toInt)
  } ensuring (_ => steps <= 1)

  @extern
  def prevCompatibleJob(i: BigInt) = {
    BigInt(p(i.toInt))
  } ensuring (res => res >= 0 && res < i && steps <= 1)

  @inline
  def max(x: BigInt, y: BigInt) = if (x >= y) x else y

  def depsEval(i: BigInt) = i == 0 || (i > 0 && allEval(i - 1))

  def allEval(i: BigInt): Boolean = {
    require(i >= 0)
    cached(sched(i)) &&
      (if (i == 0) true
      else allEval(i - 1))
  }

  @traceInduct
  def evalMono(i: BigInt, st1: Set[Fun[BigInt]], st2: Set[Fun[BigInt]]) = {
    require(i >= 0)
    (st1.subsetOf(st2) && (allEval(i) in st1)) ==> (allEval(i) in st2)
  } holds

  @traceInduct
  def evalLem(x: BigInt, y: BigInt) = {
    require(x >= 0 && y >= 0)
    (x <= y && allEval(y)) ==> allEval(x)
  } holds

  @invisibleBody
  @invstate
  @memoize
  def sched(jobIndex: BigInt): BigInt = {
    require(depsEval(jobIndex) &&
      (if(jobIndex == 0) true else evalLem(prevCompatibleJob(jobIndex), jobIndex - 1)))
    val (st, fn, w) = jobInfo(jobIndex)
    if (jobIndex == 0) w
    else {
      // we may either include the head job or not:
      // if we include the head job, we have to skip every job that overlaps with it
      val tailValue = sched(jobIndex - 1)
      val prevCompatVal = sched(prevCompatibleJob(jobIndex))
      max(w + prevCompatVal, tailValue)
    }
  } ensuring (_ => steps <= ?)

  @invisibleBody
  def invoke(jobIndex: BigInt) = {
    require(depsEval(jobIndex))
    sched(jobIndex)
  } ensuring (res => {
    val in = inSt[BigInt]
    val out = outSt[BigInt]
    (jobIndex == 0 || evalMono(jobIndex - 1, in, out)) &&
      steps <= ?
  })

  @invisibleBody
  def schedBU(jobi: BigInt): IList = {
    require(jobi >= 0)
    if (jobi == 0) {
      Cons(invoke(jobi), Nil())
    } else {
      val tailRes = schedBU(jobi - 1)
      Cons(invoke(jobi), tailRes)
    }
  } ensuring (_ => allEval(jobi) &&
    steps <= ? * jobi + ?)

  @ignore
  def main(args: Array[String]) {
    // note: we can run only one test in each run as the cache needs to be cleared between the tests,
    // which is not currently supported by the api's (note: the methods access a mutable field)
    test1()
    //test2()
  }

  @ignore
  def test1() {
    jobs = Array((0, 0, 0), (1, 2, 5), (3, 4, 2), (3, 8, 5), (6, 7, 10), (8, 11, 11), (10, 13, 20))
    p = Array(0 /* anything */ , 0, 1, 1, 2, 4, 4)
    println("Schedule for 5 jobs of set 1: " + schedBU(6))
  }

  @ignore
  def test2() {
    jobs = Array((0, 0, 0), (1, 3, 5), (3, 4, 2), (3, 8, 5), (6, 7, 10), (8, 11, 11), (10, 13, 20))
    p = Array(0 /* anything */ , 0, 0, 0, 2, 4, 4)
    println("Schedule for 5 jobs of set 2: " + schedBU(6))
  }
}
