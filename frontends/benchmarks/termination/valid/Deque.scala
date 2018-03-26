/* Copyright 2009-2018 EPFL, Lausanne */

import stainless._
import lang._
import annotation._
import collection._
import math._

/**
 * A constant time deque based on Okasaki's implementation: Fig.8.4 Pg. 112.
 * Here, both front and rear streams are scheduled.
 */
object RealTimeDeque {
  sealed abstract class Stream[T] {
    def isEmpty: Boolean = this == SNil[T]()
    def isCons: Boolean = !isEmpty

    lazy val stail: Stream[T] = {
      require(isCons)
      this match {
        case SCons(_, tfun, _) => tfun()
      }
    }

    def size = this match {
      case SCons(_, _, sz) if sz > 0 => sz
      case _ => BigInt(0)
    }

    /**
     * Asserts that the size of the tail strictly decreases
     */
    def finite: Boolean = {
      decreases(this.size)
      this match {
        case c @ SCons(_, _, sz) =>
          val tail = c.stail
          sz >= 0 && sz == tail.size + 1 && tail.finite
        case SNil() => true
      }
    }
  }

  private case class SCons[T](x: T, tfun: () => Stream[T], sz: BigInt) extends Stream[T]
  private case class SNil[T]() extends Stream[T]

  def take[T](n: BigInt, l: Stream[T]): Stream[T] = {
    require(n >= 0 && l.finite && l.size >= n)
    decreases(abs(n))
    if(n == 0) SNil[T]()
    else {
      l match {
        case SNil() => l
        case c @ SCons(x, _, _) =>
          if (n == 1)
            SCons[T](x, () => SNil[T](), BigInt(1))
          else {
            val newn = n - 1
            val t = c.stail
            SCons[T](x, () => take(newn, t), n)
          }
      }
    }
  } ensuring(res => res.finite && res.size == n)

  def revAppend[T](l1: Stream[T], l2: Stream[T]): Stream[T] = {
    require(l1.finite && l2.finite)
    decreases(l1.size)
    l1 match {
      case SNil() => l2
      case c @ SCons(x, _, _) =>
        revAppend(c.stail, SCons[T](x, () => l2, l2.size + 1))
    }
  } ensuring(res => res.finite && res.size == l1.size + l2.size)

  def drop[T](n: BigInt, l: Stream[T]): Stream[T] = {
    require(n >= 0 && l.finite && l.size >= n)
    decreases(abs(n))
    if (n == 0) l
    else {
      l match {
        case SNil()          => l
        case c @ SCons(x, _, _) => drop(n - 1, c.stail)
      }
    }
  } ensuring(res => res.finite && res.size == l.size - n)

  def rotateRev[T](r: Stream[T], f: Stream[T], a: Stream[T]): Stream[T] = {
    require (f.finite && r.finite && a.finite && {
      val lenf = f.size
      val lenr = r.size
      (lenf <= 2 * lenr + 3 && lenf >= 2 * lenr + 1)
    })
    decreases(r.size)
    r match {
      case SNil() => revAppend(f, a) // |f| <= 3
      case c @ SCons(x, _, _) =>
        val nr = c.stail
        val nf = drop(2, f)
        val na = revAppend(take(2, f), a)
        SCons(x, () => rotateRev(nr, nf, na), r.size + f.size + a.size)
    }
    // here, it doesn't matter whether 'f' has i elements or not,
    // what we want is |drop(2,f)| + |take(2,f)| == |f|

  } ensuring(res => res.finite && res.size == r.size + f.size + a.size)

  def rotateDrop[T](r: Stream[T], i: BigInt, f: Stream[T]): Stream[T] = {
    require(f.finite && r.finite && i >= 0 && {
      val lenf = f.size
      val lenr = r.size
      (lenf >= 2 * lenr + 2 && lenf <= 2 * lenr + 3) && // size invariant between 'f' and 'r'
        lenf > i
    })
    decreases(r.size)
    if (i < 2 || r == SNil[T]()) {               // A bug in Okasaki implementation: we must check for: 'rval = SNil()'
      rotateRev(r, drop(i, f), SNil[T]())
    } else {
      r match {
        case c @ SCons(x, _, _) =>
          val nr = c.stail
          val ni = i - 2
          val nf = drop(2, f)
          SCons(x, () => rotateDrop(nr, ni, nf), r.size + f.size - i)
      }
    }
  } ensuring (res => res.finite && res.size == r.size + f.size - i)

  case class Queue[T](f: Stream[T], sf: Stream[T], r: Stream[T], sr: Stream[T]) {
    def isEmpty = f.size + r.size == 0
    def valid = {
        val lenf = f.size
        val lenr = r.size
        f.finite && r.finite && (lenf <= 2 * lenr + 1 && lenr <= 2 * lenf + 1)
    }
  }

  /**
   * A function that takes streams where the size of front and rear streams violate
   * the balance invariant, and restores the balance.
   */
  def createQueue[T](f: Stream[T], sf: Stream[T], r: Stream[T], sr: Stream[T]): Queue[T] = {
    require {
      val lenf = f.size
      val lenr = r.size
      f.finite && r.finite &&
      ((lenf - 1 <= 2 * lenr + 1 && lenr <= 2 * lenf + 1) ||
          (lenf <= 2 * lenr + 1 && lenr - 2 <= 2 * lenf + 1))
    }
    val lenf = f.size
    val lenr = r.size
    if (lenf > 2 * lenr + 1) {
      val i = (lenf + lenr) / 2
      val j = lenf + lenr - i
      val nr = rotateDrop(r, i, f)
      val nf = take(i, f)
      Queue(nf, nf, nr, nr)
    } else if (lenr > 2 * lenf + 1) {
      val i = (lenf + lenr) / 2
      val j = lenf + lenr - i
      val nf = rotateDrop(f, j, r) // here, both 'r' and 'f' are concretized
      val nr = take(j, r)
      Queue(nf, nf, nr, nr)
    } else
      Queue(f, sf, r, sr)
  } ensuring (res => res.valid)

  /**
   * Forces the schedules
   */
  def force[T](tar: Stream[T]): Stream[T] = {
    tar match {
      case c @ SCons(_, _,_) => c.stail
      case _               => tar
    }
  }

  /**
   * Forces the schedules in the queue twice and ensures the `firstUneval` property.
   */
  def forceTwice[T](q: Queue[T]): (Stream[T], Stream[T]) = {
    val nsf = force(force(q.sf)) // forces q.sf twice
    val nsr = force(force(q.sr)) // forces q.sr twice
    (nsf, nsr)
  }

  def empty[T] = {
    val nil: Stream[T] = SNil[T]()
    Queue(nil, nil, nil,   nil)
  }

  def head[T](q: Queue[T]): T = {
    require(!q.isEmpty && q.valid)
    (q.f, q.r) match {
      case (SCons(x, _, _), _) => x
      case (_, SCons(x, _, _)) => x
    }
  }

  /**
   * Adding an element to the front of the list
   */
  def cons[T](x: T, q: Queue[T]): Queue[T] = {
    require(q.valid)
    // force the front and rear scheds once
    val nsf = force(q.sf)
    val nsr = force(q.sr)
    createQueue(SCons[T](x, () => q.f, 1 + q.f.size), nsf, q.r, nsr)
  } ensuring (res => res.valid)

  /**
   * Removing the element at the front, and returning the tail
   */
  def tail[T](q: Queue[T]): Queue[T] = {
    require(!q.isEmpty && q.valid)
    force(q.f) match { // the match construct guards against optimizing this away
      case _ =>
        q.f match {
          case c @ SCons(x, _, _) =>
            val (nsf, nsr) = forceTwice(q)
            createQueue(c.stail, nsf, q.r, nsr)
          case SNil() =>
            empty[T]
        }
    }
  } ensuring (res => res.valid)

  /**
   * Reversing a list. Takes constant time.
   * This implies that data structure is a `deque`.
   */
  def reverse[T](q: Queue[T]): Queue[T] = {
    require(q.valid)
    Queue(q.r, q.sr, q.f, q.sf)
  } ensuring (_ => q.valid)

  def snoc[T](x: T, q: Queue[T]): Queue[T] = {
    require(q.valid)
    reverse(cons(x, reverse(q)))
  }
}
