/* Copyright 2009-2022 EPFL, Lausanne */

package stainless
package collection

import stainless.annotation._
import stainless.lang._
import StaticChecks._

@library
object ListMapLemmas {
  import ListSpecs._

  @opaque
  def noDuplicatePairs[A, B](lm: ListMap[A, B]): Unit = {
    lm.toList match {
      case Nil() => ()
      case Cons(x, xs) =>
        noDuplicatePairs(ListMap(xs))
        tailDoesNotContainPair(lm)
    }
  }.ensuring(_ => ListOps.noDuplicate(lm.toList))

  @opaque
  def noDuplicateKeysSubseq[A, B](l1: List[(A, B)], l2: List[(A, B)]): Unit = {
    require(ListOps.noDuplicate(l2.map(_._1)))
    require(ListSpecs.subseq(l1, l2))
    decreases(l2.size)
    ((l1, l2): @unchecked) match {
      case (Nil(), _) => ()
      case (x :: xs, y :: ys) =>
        if (x == y && ListSpecs.subseq(xs, ys)) {
          noDuplicateKeysSubseq(xs, ys)
          assert(ListOps.noDuplicate(xs.map(_._1)))
          assert(!ys.map(_._1).contains(y._1))
          subseqKeys(xs, ys)
          ListSpecs.subseqNotContains(xs.map(_._1), ys.map(_._1), x._1)
          assert(!xs.map(_._1).contains(x._1))
        } else {
          assert(ListSpecs.subseq(l1, ys))
          noDuplicateKeysSubseq(l1, ys)
        }
    }
  }.ensuring(_ => ListOps.noDuplicate(l1.map(_._1)))

  @opaque
  def addValidProp[A, B](lm: ListMap[A, B], p: ((A, B)) => Boolean, a: A, b: B): Unit = {
    require(lm.forall(p) && p(a, b))
    decreases(lm.toList.size)

    if (!lm.isEmpty)
      addValidProp(lm.tail, p, a, b)

  }.ensuring { _ =>
    val nlm = lm + (a, b)
    nlm.forall(p)
  }

  @opaque
  def removeValidProp[A, B](lm: ListMap[A, B], p: ((A, B)) => Boolean, a: A): Unit = {
    require(lm.forall(p))

    listFilterValidProp(lm.toList, p, (ab: (A, B)) => ab._1 != a)

  }.ensuring { _ =>
    val nlm = lm - a
    nlm.forall(p)
  }

  @opaque
  def insertAllValidProp[A, B](lm: ListMap[A, B], kvs: List[(A, B)], p: ((A, B)) => Boolean): Unit = {
    require(lm.forall(p) && kvs.forall(p))
    decreases(kvs)

    if (!kvs.isEmpty) {
      addValidProp(lm, p, kvs.head._1, kvs.head._2)
      insertAllValidProp(lm + kvs.head, kvs.tail, p)
    }

  }.ensuring { _ =>
    val nlm = lm ++ kvs
    nlm.forall(p)
  }

  @opaque
  def removeAllValidProp[A, B](lm: ListMap[A, B], l: List[A], p: ((A, B)) => Boolean): Unit = {
    require(lm.forall(p))
    decreases(l)

    if (!l.isEmpty) {
      removeValidProp(lm, p, l.head)
      removeAllValidProp(lm - l.head, l.tail, p)
    }

  }.ensuring { _ =>
    val nlm = lm -- l
    nlm.forall(p)
  }

  @opaque
  def filterStillContains[A, B](l: List[(A, B)], a1: A, a2: A): Unit = {
    require(a1 != a2)
    decreases(l)

    if (!l.isEmpty && l.head._1 != a2)
      filterStillContains(l.tail, a1, a2)

  }.ensuring(_ =>
    l.find(_._1 == a2) == l.filter(_._1 != a1).find(_._1 == a2)
  )

  @opaque
  def addApplyDifferent[A, B](lm: ListMap[A, B], a: A, b: B, a0: A): Unit = {
    require(lm.contains(a0) && a0 != a)

    filterStillContains(lm.toList, a, a0)

  }.ensuring(_ =>
    (lm + (a -> b))(a0) == lm(a0)
  )

  @opaque
  def addStillContains[A, B](lm: ListMap[A, B], a: A, b: B, a0: A): Unit = {
    require(lm.contains(a0))

    assert(lm.get(a0).isDefined)
    assert(lm.toList.find(_._1 == a0).isDefined)

    if (a != a0)
      filterStillContains(lm.toList, a, a0)

  }.ensuring(_ =>
    (lm + (a, b)).contains(a0)
  )

  @opaque
  def applyForall[A, B](lm: ListMap[A, B], p: ((A, B)) => Boolean, k: A): Unit = {
    require(lm.forall(p) && lm.contains(k))
    decreases(lm.toList.size)

    if (!lm.isEmpty && lm.toList.head._1 != k)
      applyForall(lm.tail, p, k)

  }.ensuring(_ => p(k, lm(k)))

  @opaque
  def getForall[A, B](lm: ListMap[A, B], p: ((A, B)) => Boolean, k: A): Unit = {
    require(lm.forall(p))
    decreases(lm.toList.size)

    if (!lm.isEmpty && lm.toList.head._1 != k)
      getForall(lm.tail, p, k)

  }.ensuring(_ => lm.get(k).forall(v => p(k, v)))

  @opaque
  def findFirstContained[A, B](l: List[(A, B)], a: A): Unit = {
    require(!l.find(_._1 == a).isEmpty)
    decreases(l)

    if (!l.isEmpty && l.head._1 != a)
      findFirstContained(l.tail, a)


  }.ensuring(_ =>
    l.map(_._1).contains(a)
  )

  @opaque
  def uniqueImage[A, B](l: List[(A, B)], a: A, b: B): Unit = {
    require(noDuplicate(l.map(_._1)) && l.contains((a, b)))
    decreases(l)

    if (!l.isEmpty && l.head != (a, b)) {
      uniqueImage(l.tail, a, b)
      assert(l.tail.find(_._1 == a) == Some[(A,B)]((a, b)))
      findFirstContained(l.tail, a)
      assert(l.find(_._1 == a) == Some[(A,B)]((a, b)))
    }

  }.ensuring(_ =>
    l.find(_._1 == a) == Some[(A,B)]((a, b))
  )

  @opaque
  def uniqueImage[A, B](lm: ListMap[A, B], a: A, b: B): Unit = {
    require(lm.toList.contains((a, b)))

    uniqueImage(lm.toList, a, b)

  }.ensuring(_ =>
    lm.get(a) == Some[B](b)
  )

  def keysOfSoundLemma0[A, B](@induct l1: List[(A, B)], l2: List[(A, B)], b: B): Unit = {
    require(!l2.isEmpty && l1.forall(p => l2.tail.contains((p._1, b))))

  }.ensuring(_ =>
    l1.forall(p => l2.contains((p._1, b)))
  )

  @opaque
  def keysOfSoundLemma1[A, B](l: List[(A, B)], b: B): Unit = {
    require(l.forall(_._2 == b))

    if (!l.isEmpty) {
      keysOfSoundLemma1(l.tail, b) // gives us:
      assert(l.tail.forall(p => l.tail.contains((p._1, b))))

      keysOfSoundLemma0(l.tail, l, b) // gives us:
      assert(l.tail.forall(p => l.contains((p._1, b))))
    }

  }.ensuring(_ =>
    l.forall(p => l.contains((p._1, b)))
  )

  @opaque
  def keysOfSoundLemma2[A, B](l: List[(A, B)], lm: ListMap[A, B], b: B): Unit = {
    require {
      val filtered = lm.toList.filter(_._2 == b)
      l.forall(p => filtered.contains((p._1, b))) &&
        l.forall(filtered.contains)
    }
    decreases(l)

    val filtered = lm.toList.filter(_._2 == b)

    if (!l.isEmpty) {
      keysOfSoundLemma2(l.tail, lm, b) // gives us:
      assert(l.tail.map(_._1).forall(key => lm.get(key) == Some[B](b)))

      uniqueImage(lm, l.head._1, l.head._2) // gives us:
      assert(lm.get(l.head._1) == Some[B](l.head._2))

      forallContained(filtered, (kv: (A, B)) => kv._2 == b, l.head) // gives us:
      assert(l.head._2 == b)
    }

  }.ensuring(_ =>
    l.map(_._1).forall(key => lm.get(key) == Some[B](b))
  )

  @opaque
  def keysOfSound[A, B](lm: ListMap[A, B], value: B): Unit = {
    val filtered = lm.toList.filter(_._2 == value)

    assert(filtered.forall(_._2 == value))

    keysOfSoundLemma1(filtered, value) // gives us:
    assert(filtered.forall(p => filtered.contains((p._1, value))))

    subsetRefl(filtered) // gives us:
    assert(filtered.forall(filtered.contains))

    keysOfSoundLemma2(filtered, lm, value) // gives us:
    assert(filtered.map(_._1).forall(key => lm.get(key) == Some[B](value)))

  }.ensuring(_ =>
    lm.keysOf(value).forall(key => lm.get(key) == Some[B](value))
  )

  @opaque
  def containsByKeyEquiv[A, B](lm: ListMap[A, B], a: A): Unit = {
    lm.toList match {
      case Nil() => ()
      case Cons((x, _), xs) if x == a => ()
      case Cons(x, xs) =>
        containsByKeyEquiv(ListMap(xs), a)
    }
  }.ensuring(_ => lm.contains(a) == lm.toList.map(_._1).contains(a))

  @opaque
  def tailDoesNotContainKey[A, B](lm: ListMap[A, B]): Unit = {
    require(lm.nonEmpty)
    decreases(lm.size)
    val Cons(x, xs) = lm.toList: @unchecked
    containsByKeyEquiv(ListMap(xs), x._1)
  }.ensuring(_ => !lm.tail.contains(lm.head._1))

  @opaque
  def tailDoesNotContainPair[A, B](lm: ListMap[A, B]): Unit = {
    require(lm.nonEmpty)
    decreases(lm.size)

    def rec(x: (A, B), @induct xs: List[(A, B)]): Unit = {
      require(ListOps.noDuplicate(xs.map(_._1)))
      require(!ListMap(xs).contains(x._1))
    }.ensuring(_ => !xs.contains(x))

    (lm.toList: @unchecked) match {
      case Cons(x, xs) =>
        tailDoesNotContainKey(lm)
        rec(x, xs)
    }
  }.ensuring(_ => !lm.toList.tail.contains(lm.toList.head))

  @opaque
  def subseqKeys[A, B](l1: List[(A, B)], l2: List[(A, B)]): Unit = {
    require(ListOps.noDuplicate(l1.map(_._1)))
    require(ListOps.noDuplicate(l2.map(_._1)))
    require(ListSpecs.subseq(l1, l2))
    decreases(l2.size)
    ((l1, l2): @unchecked) match {
      case (Nil(), _) => ()
      case (x :: xs, y :: ys) =>
        if (x == y && ListSpecs.subseq(xs, ys)) {
          subseqKeys(xs, ys)
        } else {
          assert(ListSpecs.subseq(l1, ys))
          subseqKeys(l1, ys)
        }
    }
  }.ensuring(_ => ListSpecs.subseq(l1.map(_._1), l2.map(_._1)))
}
