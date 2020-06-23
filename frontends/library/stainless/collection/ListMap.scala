package stainless
package collection

import stainless.annotation._
import stainless.lang._

/** Ordered list-backed Map implementation */

@library
case class ListMap[A, B](toList: List[(A, B)]) {
  require(ListOps.noDuplicate(toList.map(_._1)))

  def isEmpty: Boolean = toList.isEmpty

  def head: (A, B) = {
    require(!isEmpty)
    toList.head
  }

  def tail: ListMap[A, B] = {
    require(!isEmpty)
    ListMap(toList.tail)
  }

  def contains(key: A): Boolean = {
    get(key).isDefined
  }

  def get(key: A): Option[B] = {
    toList.find(_._1 == key).map(_._2)
  }

  def keysOf(value: B): List[A] = {
    toList.filter(_._2 == value).map(_._1)
  }

  def apply(key: A): B = {
    require(contains(key))
    get(key).get
  }

  def +(keyValue: (A, B)): ListMap[A, B] = {
    ListSpecs.filterMapNotIn(toList, keyValue._1) // gives us:
    assert(!toList.filter(_._1 != keyValue._1).map(_._1).contains(keyValue._1))

    ListSpecs.noDuplicateMapFilter(toList, (kv: (A, B)) => kv._1 != keyValue._1, (kv: (A, B)) => kv._1) // gives us:
    assert(ListSpecs.noDuplicate(toList.filter(_._1 != keyValue._1).map(_._1)))

    ListMap(keyValue :: toList.filter(_._1 != keyValue._1))
  }

  def ++(keyValues: List[(A, B)]): ListMap[A, B] = {
    decreases(keyValues)
    keyValues match {
      case Nil()                => this
      case Cons(keyValue, rest) => (this + keyValue) ++ rest
    }
  }

  def -(key: A): ListMap[A, B] = {
    if (contains(key)) {
      ListSpecs.noDuplicateMapFilter(toList, (kv: (A, B)) => kv._1 != key, (kv: (A, B)) => kv._1)
      ListMap(toList.filter(_._1 != key))
    } else {
      this
    }
  }

  def --(keys: List[A]): ListMap[A, B] = keys match {
    case Nil()           => this
    case Cons(key, rest) => (this - key) -- rest
  }

  def forall(p: ((A, B)) => Boolean): Boolean = {
    toList.forall(p)
  }
}

@library
object ListMap {
  def empty[A, B]: ListMap[A, B] = ListMap(List.empty[(A, B)])
}

@library
object ListMapLemmas {
  import ListSpecs._

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
}
