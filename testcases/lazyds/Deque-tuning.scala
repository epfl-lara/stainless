package withOrb

import leon._
import mem._
import higherorder._
import lang._
import annotation._
import collection._
import instrumentation._
import math._
import invariant._

/**
 * A constant time deque based on Okasaki's implementation: Fig.8.4 Pg. 112.
 * Here, both front and rear streams are scheduled.
 * We require both the front and the rear streams to be of almost equal
 * size. If not, we lazily rotate the streams.
 * The invariants are a lot more complex than in `RealTimeQueue`.
 * The program also fixes a bug in Okasaki's implementatin: see function `rotateDrop`.
 * Proof Hint: requires unrollfactor = 4
 */
object RealTimeDeque {
  sealed abstract class Stream[T] {
    @inline
    def isEmpty: Boolean = this == SNil[T]()
    @inline
    def isCons: Boolean = !isEmpty

    def size: BigInt = {
      this match {
        case SNil()          => BigInt(0)
        case t @ SCons(_, _) => 1 + t.stailVal.size
      }
    } ensuring (_ >= 0)

    @inline
    def stail: Stream[T] = {
      this match {
        case SCons(_, Val(x))     => x
        case SCons(_, f @ Fun(_)) => f.get
      }
    }

    @inline
    def stailVal: Stream[T] = {
      this match {
        case SCons(_, Val(x))     => x
        case SCons(_, f @ Fun(_)) => f.get*
      }
    }

    @inline
    def tailCached: Boolean = {
      this match {
        case SCons(_, f: Fun[T]) => f.get.cached
        case _                   => true
      }
    }
  }

  private case class SCons[T](x: T, next: ValOrFun[T]) extends Stream[T]
  private case class SNil[T]() extends Stream[T]

  sealed abstract class ValOrFun[T] {
    lazy val get: Stream[T] = {
      this match {
        case Fun(f) => f()
        case Val(x) => x
      }
    }
  }
  private case class Val[T](x: Stream[T]) extends ValOrFun[T]
  private case class Fun[T](fun: () => Stream[T]) extends ValOrFun[T]

  def isConcrete[T](l: Stream[T]): Boolean = {
    l match {
      case c @ SCons(_, _) =>
        c.tailCached && isConcrete(c.stailVal)
      case _ => true
    }
  }

  @invstate
  def takeLazy[T](n: BigInt, l: Stream[T]): Stream[T] = {
    require(isConcrete(l) && n >= 1 && l.size >= n)
    l match {
      case c @ SCons(x, _) =>
        if (n == 1)
          SCons[T](x, Val[T](SNil[T]()))
        else {
          val newn = n - 1
          val t = c.stail
          SCons[T](x, Fun[T](() => takeLazy(newn, t)))
        }
    }
  } ensuring (res => res.size == n && res.isCons &&
    time <= ?)

  @invstate
  def revAppend[T](l1: Stream[T], l2: Stream[T]): Stream[T] = {
    require(isConcrete(l1) && isConcrete(l2))
    l1 match {
      case SNil() => l2
      case c @ SCons(x, _) =>
        revAppend(c.stail, SCons[T](x, Val(l2)))
    }
  } ensuring (res => res.size == l1.size + l2.size &&
    isConcrete(res) &&
    (l1.size >= 1 ==> res.isCons) &&
    time <= ? * l1.size + ?)

  @invstate
  def drop[T](n: BigInt, l: Stream[T]): Stream[T] = {
    require(n >= 0 && isConcrete(l) && l.size >= n)
    if (n == 0) l
    else {
      l match {
        case SNil()          => l
        case c @ SCons(x, _) => drop(n - 1, c.stail)
      }
    }
  } ensuring (res => isConcrete(res) &&
    res.size == l.size - n &&
    time <= ? * n + ?)

  @invstate
  def take[T](n: BigInt, l: Stream[T]): Stream[T] = {
    require(n >= 0 && isConcrete(l) && l.size >= n)
    if (n == 0) SNil[T]()
    else {
      l match {
        case SNil() => l
        case c @ SCons(x, _) =>
          SCons[T](x, Val(take(n - 1, c.stail)))
      }
    }
  } ensuring (res => isConcrete(res) &&
    res.size == n &&
    time <= ? * n + ?)

  @invstate
  def rotateRev[T](r: Stream[T], f: Stream[T], a: Stream[T]): Stream[T] = {
    require(isConcrete(r) && isConcrete(f) && isConcrete(a) &&
      {
        val lenf = f.size
        val lenr = r.size
        (lenf <= 2 * lenr + 3 && lenf >= 2 * lenr + 1)
      })
    r match {
      case SNil() => revAppend(f, a) // |f| <= 3
      case c @ SCons(x, _) =>
        val nr = c.stail
        val nf = drop(2, f)
        val na = revAppend(take(2, f), a)
        SCons(x, Fun(() => rotateRev(nr, nf, na)))
    } // here, it doesn't matter whether 'f' has i elements or not, what we want is |drop(2,f)| + |take(2,f)| == |f|
  } ensuring (res => res.size == r.size + f.size + a.size &&
    res.isCons &&
    time <= ?)

  @invstate
  def rotateDrop[T](r: Stream[T], i: BigInt, f: Stream[T]): Stream[T] = {
    require(isConcrete(r) && isConcrete(f) && i >= 0 && {
      val lenf = f.size
      val lenr = r.size
      (lenf >= 2 * lenr + 2 && lenf <= 2 * lenr + 3) && // size invariant between 'f' and 'r'
        lenf > i
    })
    if (i < 2 || r == SNil[T]()) { // A bug in Okasaki implementation: we must check for: 'rval = SNil()'
      rotateRev(r, drop(i, f), SNil[T]())
    } else {
      r match {
        case c @ SCons(x, _) =>
          val nr = c.stail
          val ni = i - 2
          val nf = drop(2, f)
          SCons(x, Fun(() => rotateDrop(nr, ni, nf)))
      }
    }
  } ensuring (res => res.size == r.size + f.size - i &&
    res.isCons && time <= ?)

  def firstUneval[T](l: Stream[T]): Stream[T] = {
    l match {
      case c @ SCons(_, _) =>
        if (c.tailCached)
          firstUneval(c.stailVal)
        else l
      case _ => l
    }
  } ensuring (res => (!res.isEmpty || isConcrete(l)) && //if there are no lazy closures then the stream is concrete
    (res.isEmpty || !res.tailCached) && // if the return value is not a Nil closure then it would not have been evaluated
    (res match {
      case c @ SCons(_, _) =>
        firstUneval(l) == firstUneval(c.stail) // after evaluating the firstUnevaluated closure in 'l' we can access the next unevaluated closure
      case _ => true
    }))

  case class Queue[T](f: Stream[T], lenf: BigInt, sf: Stream[T],
                      r: Stream[T], lenr: BigInt, sr: Stream[T]) {
    def isEmpty = lenf + lenr == 0
    def valid = {
      (firstUneval(f) == firstUneval(sf)) &&
        (firstUneval(r) == firstUneval(sr)) &&
        (lenf == f.size && lenr == r.size) &&
        (lenf <= 2 * lenr + 1 && lenr <= 2 * lenf + 1) &&
        {
          val mind = min(2 * lenr - lenf + 2, 2 * lenf - lenr + 2)
          sf.size <= mind && sr.size <= mind
        }
    }
  }

  /**
   * A function that takes streams where the size of front and rear streams violate
   * the balance invariant, and restores the balance.
   */
  @invisibleBody
  def createQueue[T](f: Stream[T], lenf: BigInt, sf: Stream[T],
                     r: Stream[T], lenr: BigInt, sr: Stream[T]): Queue[T] = {
    require(firstUneval(f) == firstUneval(sf) &&
      firstUneval(r) == firstUneval(sr) &&
      (lenf == f.size && lenr == r.size) &&
      ((lenf - 1 <= 2 * lenr + 1 && lenr <= 2 * lenf + 1) ||
        (lenf <= 2 * lenr + 1 && lenr - 2 <= 2 * lenf + 1)) &&
        {
          val mind = max(min(2 * lenr - lenf + 2, 2 * lenf - lenr + 2), 0)
          sf.size <= mind && sr.size <= mind
        })
    if (lenf > 2 * lenr + 1) {
      val i = (lenf + lenr) / 2
      val j = lenf + lenr - i
      val nr = rotateDrop(r, i, f)
      val nf = takeLazy(i, f)
      Queue(nf, i, nf, nr, j, nr)
    } else if (lenr > 2 * lenf + 1) {
      val i = (lenf + lenr) / 2
      val j = lenf + lenr - i
      val nf = rotateDrop(f, j, r) // here, both 'r' and 'f' are concretized
      val nr = takeLazy(j, r)
      Queue(nf, i, nf, nr, j, nr)
    } else
      Queue(f, lenf, sf, r, lenr, sr)
  } ensuring (res => res.valid &&
    time <= ?)

  @invisibleBody
  def funeEqual[T](s1: Stream[T], s2: Stream[T]) = firstUneval(s1) == firstUneval(s2)

  /**
   * Forces the schedules, and ensures that `firstUneval` equality is preserved
   */
  @invisibleBody
  def force[T](tar: Stream[T], htar: Stream[T], other: Stream[T], hother: Stream[T]): Stream[T] = {
    require(funeEqual(tar, htar) && funeEqual(other, hother))
    tar match {
      case c @ SCons(_, _) => c.stail
      case _               => tar
    }
  } ensuring (res => {
    //lemma instantiations
    val in = inState[T]
    val out = outState[T]
    funeMonotone(tar, htar, in, out) &&
      funeMonotone(other, hother, in, out) && {
        //properties
        val rsize = res.size
        firstUneval(htar) == firstUneval(res) && // follows from post of fune
          firstUneval(other) == firstUneval(hother) &&
          (rsize == 0 || rsize == tar.size - 1)
      } && time <= ?
  })

  /**
   * Forces the schedules in the queue twice and ensures the `firstUneval` property.
   */
  @invisibleBody
  def forceTwice[T](q: Queue[T]): (Stream[T], Stream[T]) = {
    require(q.valid)
    val nsf = force(force(q.sf, q.f, q.r, q.sr), q.f, q.r, q.sr) // forces q.sf twice
    val nsr = force(force(q.sr, q.r, q.f, nsf), q.r, q.f, nsf) // forces q.sr twice
    (nsf, nsr)
  } ensuring (_ => time <= ?)
  // the following properties are ensured, but need not be stated
  /*ensuring (res => {
    val nsf = res._1
    val nsr = res._2
    firstUneval(q.f) == firstUneval(nsf) &&
      firstUneval(q.r) == firstUneval(nsr) &&
      (ssize(nsf) == 0 || ssize(nsf) == ssize(q.sf) - 2) &&
      (ssize(nsr) == 0 || ssize(nsr) == ssize(q.sr) - 2) &&
      time <= 1500
  })*/

  def empty[T] = {
    val nil: Stream[T] = SNil[T]()
    Queue(nil, 0, nil, nil, 0, nil)
  }

  def head[T](q: Queue[T]): T = {
    require(!q.isEmpty && q.valid)
    (q.f, q.r) match {
      case (SCons(x, _), _) => x
      case (_, SCons(x, _)) => x
    }
  }

  /**
   * Adding an element to the front of the list
   */
  def cons[T](x: T, q: Queue[T]): Queue[T] = {
    require(q.valid)
    // force the front and rear scheds once
    val nsf = force(q.sf, q.f, q.r, q.sr)
    val nsr = force(q.sr, q.r, q.f, nsf)
    createQueue(SCons[T](x, Val(q.f)), q.lenf + 1, nsf, q.r, q.lenr, nsr)
  } ensuring (res => res.valid && time <= ?)

  /**
   * Removing the element at the front, and returning the tail
   */
  def tail[T](q: Queue[T]): Queue[T] = {
    require(!q.isEmpty && q.valid)
    force(q.f, q.sf, q.r, q.sr) match { // force 'f'
      case _ =>
        tailSub(q)
    }
  } ensuring (res => res.valid && time <= ?)

  def tailSub[T](q: Queue[T]): Queue[T] = {
    require(!q.isEmpty && q.valid && q.f.tailCached)
    q.f match {
      case c @ SCons(x, _) =>
        val (nsf, nsr) = forceTwice(q)
        // here, sf and sr got smaller by 2 holds, the schedule invariant still holds
        createQueue(c.stail, q.lenf - 1, nsf, q.r, q.lenr, nsr)
      case SNil() =>
        // in this case 'r' will have only one element by invariant
        empty[T]
    }
  } ensuring (res => res.valid && time <= ?)

  /**
   * Reversing a list. Takes constant time.
   * This implies that data structure is a `deque`.
   */
  def reverse[T](q: Queue[T]): Queue[T] = {
    require(q.valid)
    Queue(q.r, q.lenr, q.sr, q.f, q.lenf, q.sf)
  } ensuring (_ => q.valid && time <= ?)

  def snoc[T](x: T, q: Queue[T]): Queue[T] = {
    require(q.valid)
    reverse(cons(x, reverse(q)))
  }

  // Properties of `firstUneval`. We use `fune` as a shorthand for `firstUneval`
  /**
   * st1.subsetOf(st2) ==> fune(l, st2) == fune(fune(l, st1), st2)
   */
  @traceInduct
  def funeCompose[T](l1: Stream[T], st1: Set[mem.Fun[T]], st2: Set[mem.Fun[T]]): Boolean = {
    require(st1.subsetOf(st2))
    // property
    (firstUneval(l1) withState st2) == (firstUneval(firstUneval(l1) withState st1) withState st2)
  } holds

  /**
   * st1.subsetOf(st2) && fune(la,st1) == fune(lb,st1) ==> fune(la,st2) == fune(lb,st2)
   * The `fune` equality  is preseved by evaluation of lazy closures.
   * This is a kind of frame axiom for `fune` but is slightly different in that
   * it doesn't require (st2 \ st1) to be disjoint from la and lb.
   */
  def funeMonotone[T](l1: Stream[T], l2: Stream[T], st1: Set[mem.Fun[T]], st2: Set[mem.Fun[T]]): Boolean = {
    require((firstUneval(l1) withState st1) == (firstUneval(l2) withState st1) &&
      st1.subsetOf(st2))
    funeCompose(l1, st1, st2) && // lemma instantiations
      funeCompose(l2, st1, st2) &&
      (firstUneval(l1) withState st2) == (firstUneval(l2) withState st2) // property
  } holds

  @ignore
  def main(args: Array[String]) {
    //import eagerEval.AmortizedQueue
    import scala.util.Random
    import scala.math.BigInt
    import stats._
    import collection._

    println("Running Deque test...")
    val ops = 2000000
    val rand = Random
    // initialize to a queue with one element (required to satisfy preconditions of dequeue and front)
    var rtd = empty[BigInt]
    //var amq = AmortizedQueue.Queue(AmortizedQueue.Nil(), AmortizedQueue.Nil())
    var totalTime1 = 0L
    var totalTime2 = 0L
    println(s"Testing amortized emphemeral behavior on $ops operations...")
    for (i <- 0 until ops) {
      if (!rtd.isEmpty) {
        val h1 = head(rtd)
        //val h2 = amq.head
        //assert(h1 == h2, s"Eager head: $h2 Lazy head: $h1")
      }
      rand.nextInt(3) match {
        case x if x == 0 => //add to rear
          //println("Enqueue..")
          rtd = timed { snoc(BigInt(i), rtd) } { totalTime1 += _ }
        //amq = timed { amq.enqueue(BigInt(i)) } { totalTime2 += _ }
        case x if x == 1 => // remove from front
          if (!rtd.isEmpty) {
            //if(i%100000 == 0)
            //println("Dequeue..")
            rtd = timed { tail(rtd) } { totalTime1 += _ }
            //amq = timed { amq.dequeue } { totalTime2 += _ }
          }
        case x if x == 2 => // reverse
          //if(i%100000 == 0)
          //println("reverse..")
          rtd = timed { reverse(rtd) } { totalTime1 += _ }
        //amq = timed { amq.reverse } { totalTime2 += _ }
      }
    }
    println(s"Ephemeral Amortized Time - Eager: ${totalTime2 / 1000.0}s Lazy: ${totalTime1 / 1000.0}s")
  }
}
