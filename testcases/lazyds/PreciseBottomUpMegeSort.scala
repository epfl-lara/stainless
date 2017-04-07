//package withOrb

import leon._
import lang._
import annotation._
import instrumentation._
import invariant._
import mem._
import higherorder._
import stats._

/**
 * Computing the kthe min using a version of merge sort that operates bottom-up.
 * This allows accessing the first element in the sorted list in O(n) time,
 * and kth element in O(kn) time.
 * Needs unrollfactor = 3
 */
object BottomUpMergeSortPrecise {

  @inline
  def max(x:BigInt, y:BigInt) = if (x >= y) x else y

  sealed abstract class List[T] {
    // size is used in the specs
    def size: BigInt = (this match {
      case Nil() => BigInt(0)
      case Cons(h, t) => 1 + t.size
    }) ensuring (_ >= 0)

    // length is used in the implementation
    val length: BigInt = (this match {
      case Nil() => BigInt(0)
      case Cons(h, t) => 1 + t.length
    }) ensuring (_ == size)
  }
  case class Cons[T](x: T, tail: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

  private sealed abstract class LList {
    def size: BigInt = {
      this match {
        case SCons(_, t) => 1 + t.size
        case _            => BigInt(0)
      }
    } ensuring (_ >= 0)

    def height: BigInt = {
      this match {
        case SCons(_, t) => t.height
        case _            => BigInt(0)
      }
    } ensuring(_ >= 0)

    def weightBalanced: Boolean = {
      this match {
        case SCons(_, t) => t.weightBalanced
        case _            => true
      }
    }
  }
  private case class SCons(x: BigInt, tailFun: Stream) extends LList
  private case class SNil() extends LList
  private case class Stream(lfun: () => LList) {
    @inline
    def size = (list*).size
    lazy val list: LList = lfun()

    def height: BigInt = {
      (lfun fmatch[LList, Stream, BigInt] {
        case (a, b) if lfun.is(() => mergeSusp(a, b)) => 1 + max(a.height, b.height)
        case _ => BigInt(0)
      }): BigInt
    }ensuring(_ >= 0)

    @invisibleBody
    def weightBalanced: Boolean = {
      lfun fmatch[LList, Stream, Boolean] {
        case (a, b) if lfun.is(() => mergeSusp(a, b)) =>
          val asz = a.size
          val bsz = b.size
          asz > 0 && asz >= bsz && (asz - bsz) <= 2 &&
          a.weightBalanced && b.weightBalanced
        case _ => true
      }
    }
  }

  @inline
  private val nilStream: Stream = Stream(() => SNil())

  /**
   * A function that computes 3 + log_2(x) for x >= 1
   * The function is defined as 1 for negative values, and 2 for zero.
   */
  def log(x: BigInt) : BigInt = {
    if(x < 0) BigInt(1)
    else if(x == 0) BigInt(2)
    else
      1 + log(x/2)
  } ensuring(_ >= 1)

  @invisibleBody
  def logMonotonicity(x: BigInt, y: BigInt): Boolean = {
    require(x <= y)
    (if(x <= 0) true
    else logMonotonicity(x / 2, y / 2)) && log(x) <= log(y)
  } holds

  @inline
  def recSizePost(l: Stream, res: BigInt): Boolean = {
    l.lfun fmatch[LList, Stream, Boolean] {
      case (a, b) if l.lfun.is(() => mergeSusp(a, b)) =>
        val asz = recSizeL(a) -2
        val bsz = recSize(b) - 1
        logMonotonicity(2 * asz, res - 1) &&
        logMonotonicity(2 * bsz, res - 1)
      case _ => true
    }
  }
    // the following facts necessary for proving the logarithmic bounds are automatically inferred, but are stated here for the record
  /*2 * asz <= res - 1 &&
  2 * bsz <= res - 1 &&*/
  /*(if(asz >= 1) {
    log(asz) + 1 <= log(res - 1)
  } else
    a.height <= log(res - 1) - 1) &&
  (if(bsz >= 1) {
    log(bsz) + 1 <= log(res - 1)
  } else
    b.height <= log(res - 1) - 1)*/

  @inline
  def recSizeL(l: LList): BigInt = {
    l match {
      case SCons(_, t) => 1 + recSize(t)
    }
  }

  @invisibleBody
  def recSize(l: Stream): BigInt = {
    require(l.weightBalanced)
    (l.lfun fmatch[LList, Stream, BigInt] {
      case (a, b) if l.lfun.is(() => mergeSusp(a, b)) => recSizeL(a) + recSize(b)
      case _ => BigInt(0)
    }) : BigInt
  } ensuring (res => l.size == res && recSizePost(l, res) && l.height <= log(res - 1))

  @invisibleBody
  def logHeightProperty(l: LList): Boolean = {
    require(l.weightBalanced)
    val lsz = l.size
    (l match {
      case SNil() => true
      case SCons(_, t) =>
        recSize(t) == t.size
    }) &&
    logMonotonicity(lsz - 2, lsz - 1) &&
    l.height <= log(lsz - 1)
  } holds

  /**
   *
   * this method is a functional implementation of buildheap in linear time.
   */
  @invisibleBody
  private def constructMergeTree(l: List[BigInt], from: BigInt, to: BigInt): (LList, List[BigInt]) = {
    require(from <= to && from >= 0 && (to - from + 1) <= l.size )
    l match {
      case Nil()           => (SNil(), Nil[BigInt]()) // this case is unreachable
      case Cons(x, tail)  =>
        if(from == to) (SCons(x, nilStream), tail)
        else {
          val mid = (from + to) / 2
          val (lside, midlist) = constructMergeTree(l, from, mid)
          val (rside, rest) = constructMergeTree(midlist, mid + 1, to)
          (merge(lside, rside), rest)
        }
    }
  } ensuring{ res =>
    val range = to - from + 1
    val (reslist, rest) = res
    reslist.size == range &&
    rest.size == l.size - range  &&
    reslist.weightBalanced &&
    steps <= ? * range + ? // 56 * to - 56 * from + 12  TODO: check why making the sign of the constant term form plus to minus fails a requirement
  }

  @invisibleBody
  private def merge(a: LList, b: LList): LList = {
    b match {
      case SNil() => a
      case SCons(x, xs) =>
        a match {
          case SNil() => b
          case SCons(y, ys) =>
            if (y < x)
              SCons(y, Stream(() => mergeSusp(b, ys))) // here, the order of arguments is changed, the sort is not a stable sort
            else
              SCons(x, Stream(() => mergeSusp(a, xs)))
        }
    }
  } ensuring{res => a.size + b.size == res.size &&
    steps <= ? // steps <= 16
  }

  /**
   *  A function that merges two sorted streams of integers.
   *  Note: the sorted stream of integers may by recursively constructed using merge.
   *  Takes steps linear in the size of the streams (non-trivial to prove due to cascading of lazy calls)
   */
  @invisibleBody
  private def mergeSusp(a: LList, b: Stream): LList = {
    require(a != SNil())
    merge(a, b.list)
  } ensuring {res =>
    res != SNil() &&
    res.height <= max(a.height, b.height) + 1 &&
    steps <= ? * b.height + ? // 22 * b.height + 23
  }

  /**
   * Takes list of integers and returns a sorted stream of integers.
   * Takes steps linear in the size of the  input since it sorts lazily.
   */
  @invisibleBody
  private def mergeSort(l: List[BigInt]): LList = {
    l match {
      case Nil() => SNil()
      case _ => constructMergeTree(l, 0, l.length - 1)._1
    }
  } ensuring (res => res.weightBalanced &&
      logHeightProperty(res) &&
      l.size == res.size &&
      res.height <= log(l.size - 1) &&
      steps <= ? * l.size + ?) // 56 * l.size + 3

  private def kthMinRec(l: LList, k: BigInt): BigInt = { // note: making this invisibleBody breaks lemms instantiation, why ?
    require(k >= 0)
    l match {
      case SCons(x, xs) =>
        if (k == 0) x
        else
          kthMinRec(xs.list, k - 1)
      case SNil() => BigInt(0)
    }
  } ensuring (_ => steps <= ? * (k * l.height) + ?) //  steps <= 36 * (k * l.height) + 17

  /**
   * A function that accesses the kth element of a list using lazy sorting.
   */
  def kthMin(l: List[BigInt], k: BigInt): BigInt = {
    require(k >= 0)
    kthMinRec(mergeSort(l), k)
  } ensuring(_ => steps <= ? * (k * log(l.size - 1)) + ? * (l.size) + ?) // 36 * (k * log(l.size - 1)) + 56 * l.size + 22

  @ignore
  def main(args: Array[String]) {
    //import eagerEval.MergeSort
    import scala.util.Random
    import scala.math.BigInt
    import stats._

    println("Running merge sort test...")
    val length = 3000000
    val maxIndexValue = 100
    val randomList = Random.shuffle((0 until length).toList)
    val l1 = randomList.foldRight(List[BigInt]()){
      case (i, acc) => BigInt(i) :: acc
    }
    val l2 = randomList.foldRight(Nil[BigInt](): List[BigInt]){
      case (i, acc) => Cons(BigInt(i), acc)
    }
    println(s"Created inputs of size (${l1.size},${l2.size}), starting operations...")
    val sort2 = timed{ mergeSort(l2) }{t => println(s"Lazy merge sort completed in ${t/1000.0} sec") }
    //val sort1 = timed{ MergeSort.msort((x: BigInt, y: BigInt) => x <= y)(l1) } {t => println(s"Eager merge sort completed in ${t/1000.0} sec") }
    // sample 10 elements from a space of [0-100]
    val rand = Random
    var totalTime1 = 0L
    var totalTime2 = 0L
    for(i <- 0 until 10) {
      val idx = rand.nextInt(maxIndexValue)
      //val e1 = timed { sort1(idx) } { totalTime1 +=_ }
      //val e2 = timed { kthMin(sort2, idx) }{ totalTime2 += _ }
      //println(s"Element at index $idx - Eager: $e1 Lazy: $e2")
      //assert(e1 == e2)
    }
    println(s"Time-taken to pick first 10 minimum elements - Eager: ${totalTime1/1000.0}s Lazy: ${totalTime2/1000.0}s")
  }
}
