/* Copyright 2009-2022 EPFL, Lausanne */

package stainless
package collection

import stainless.annotation._
import stainless.lang._
import StaticChecks._
import stainless.collection.TupleListOpsGenK

@library
object ListMapLemmas {

  @opaque
  @inlineOnce
  def removeNotPresentStillSame[K, B](lm: ListMap[K, B], a: K): Unit = {
    require(!lm.contains(a))
    TupleListOpsGenK.lemmaremovePresrvNoDuplicatedKeysNotPresentPreserves(lm.toList, a)
  }.ensuring(_ => lm - a == lm)

  @opaque
  @inlineOnce
  def addSameAsAddTwiceSameKeyDiffValues[K, B](
      lm: ListMap[K, B],
      a: K,
      b1: B,
      b2: B
  ): Unit = {
    TupleListOpsGenK.lemmainsertNoDuplicatedKeysErasesIfSameKey(lm.toList, a, b1, b2)
  }.ensuring(_ => lm + (a, b2) == (lm + (a, b1) + (a, b2)))

  @opaque
  @inlineOnce
  def addRemoveCommutativeForDiffKeys[K, B](
      lm: ListMap[K, B],
      a1: K,
      b1: B,
      a2: K
  ): Unit = {
    require(a1 != a2)
    TupleListOpsGenK.lemmaInsertAndremovePresrvNoDuplicatedKeysCommutative(
      lm.toList,
      a1,
      b1,
      a2
    )
  }.ensuring(_ => lm + (a1, b1) - a2 == lm - a2 + (a1, b1))

  @opaque
  @inlineOnce
  def addThenRemoveForNewKeyIsSame[K, B](
      lm: ListMap[K, B],
      a1: K,
      b1: B
  ): Unit = {
    require(!lm.contains(a1))
    TupleListOpsGenK.lemmainsertNoDuplicatedKeysThenRemoveIsSame(lm.toList, a1, b1)
  }.ensuring(_ => lm + (a1, b1) - a1 == lm)

  @opaque
  @inlineOnce
  def removeThenAddForSameKeyIsSameAsAdd[K, B](
      lm: ListMap[K, B],
      a1: K,
      b1: B
  ): Unit = {
    TupleListOpsGenK.lemmaRemoveTheninsertNoDuplicatedKeysIsSameAsInsert(lm.toList, a1, b1)
  }.ensuring(_ => (lm - a1 + (a1, b1)).eq(lm + (a1, b1)))

  @opaque
  @inlineOnce
  def removeCommutative[K, B](lm: ListMap[K, B], a1: K, a2: K): Unit = {
    TupleListOpsGenK.lemmaremovePresrvNoDuplicatedKeysCommutative(lm.toList, a1, a2)
  }.ensuring(_ => lm - a1 - a2 == lm - a2 - a1)

  @opaque
  @inlineOnce
  def addCommutativeForDiffKeys[K, B](
      lm: ListMap[K, B],
      a1: K,
      b1: B,
      a2: K,
      b2: B
  ): Unit = {
    require(a1 != a2)
    TupleListOpsGenK.lemmainsertNoDuplicatedKeysCommutative(lm.toList, a1, b1, a2, b2)
  }.ensuring(_ => (lm + (a1, b1) + (a2, b2)).eq(lm + (a2, b2) + (a1, b1)))

  @opaque
  @inlineOnce
  def addValidProp[K, B](
      lm: ListMap[K, B],
      p: ((K, B)) => Boolean,
      a: K,
      b: B
  ): Unit = {
    require(lm.forall(p) && p(a, b))
    decreases(lm.toList.size)

    if (!lm.isEmpty)
      addValidProp(lm.tail, p, a, b)

  }.ensuring { _ =>
    val nlm = lm + (a, b)
    nlm.forall(p)
  }

  @opaque
  @inlineOnce
  def removeValidProp[K, B](
      lm: ListMap[K, B],
      p: ((K, B)) => Boolean,
      a: K
  ): Unit = {
    require(lm.forall(p))
    decreases(lm.toList.size)
    if (!lm.isEmpty)
      removeValidProp(lm.tail, p, a)

  }.ensuring { _ =>
    val nlm = lm - a
    nlm.forall(p)
  }

  @opaque
  @inlineOnce
  def insertAllValidProp[K, B](
      lm: ListMap[K, B],
      kvs: List[(K, B)],
      p: ((K, B)) => Boolean
  ): Unit = {
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
  @inlineOnce
  def removeAllValidProp[K, B](
      lm: ListMap[K, B],
      l: List[K],
      p: ((K, B)) => Boolean
  ): Unit = {
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
  @inlineOnce
  def addApplyDifferent[K, B](
      lm: ListMap[K, B],
      a: K,
      b: B,
      a0: K
  ): Unit = {
    require(lm.contains(a0) && a0 != a)
    assert(TupleListOpsGenK.containsKey(lm.toList, a0))
    TupleListOpsGenK.lemmainsertNoDuplicatedKeysDoesNotModifyOtherKeyValues(
      lm.toList,
      a,
      b,
      a0
    )
    TupleListOpsGenK.lemmaContainsKeyImpliesGetValueByKeyDefined(lm.toList, a0)

  }.ensuring(_ => (lm + (a -> b)).apply(a0) == lm(a0))

  @opaque
  @inlineOnce
  def addStillContains[K, B](
      lm: ListMap[K, B],
      a: K,
      b: B,
      a0: K
  ): Unit = {
    require(lm.contains(a0))

    if (a != a0)
      TupleListOpsGenK.lemmainsertNoDuplicatedKeysDoesNotModifyOtherKeysContained(
        lm.toList,
        a,
        b,
        a0
      )

  }.ensuring(_ => (lm + (a, b)).contains(a0))

  @opaque
  @inlineOnce
  def addStillNotContains[K, B](
      lm: ListMap[K, B],
      a: K,
      b: B,
      a0: K
  ): Unit = {
    require(!lm.contains(a0) && a != a0)

    TupleListOpsGenK.lemmainsertNoDuplicatedKeysDoesNotModifyOtherKeysNotContained(
      lm.toList,
      a,
      b,
      a0
    )

  }.ensuring(_ => !(lm + (a, b)).contains(a0))

  @opaque
  @inlineOnce
  def applyForall[K, B](
      lm: ListMap[K, B],
      p: ((K, B)) => Boolean,
      k: K
  ): Unit = {
    require(lm.forall(p) && lm.contains(k))
    decreases(lm.toList.size)

    if (!lm.isEmpty && lm.toList.head._1 != k)
      applyForall(lm.tail, p, k)

  }.ensuring(_ => p(k, lm(k)))

  @opaque
  @inlineOnce
  def getForall[K, B](
      lm: ListMap[K, B],
      p: ((K, B)) => Boolean,
      k: K
  ): Unit = {
    require(lm.forall(p))
    decreases(lm.toList.size)

    if (!lm.isEmpty && lm.toList.head._1 != k)
      getForall(lm.tail, p, k)

  }.ensuring(_ => lm.get(k).forall(v => p(k, v)))

  @opaque
  @inlineOnce
  def uniqueImage[K, B](lm: ListMap[K, B], a: K, b: B): Unit = {
    require(lm.toList.contains((a, b)))

    TupleListOpsGenK.lemmaContainsTupleThenContainsKey(lm.toList, a, b)
    TupleListOpsGenK.lemmaContainsTupThenGetReturnValue(lm.toList, a, b)

  }.ensuring(_ => lm.get(a) == Some[B](b))

  @opaque
  @inlineOnce
  def lemmaContainsAllItsOwnKeys[K, B](lm: ListMap[K, B]): Unit = {
    decreases(lm.toList.size)
    lm.toList match
      case Cons(h, t) => {
        lemmaContainsAllItsOwnKeys(ListMap(t))
        assert(t.forall(p => ListMap(t).contains(p._1)))
        assert(lm == ListMap(t) + h)
        lemmaInsertPairStillContainsAll(ListMap(t), t, h._1, h._2)
        lemmaInsertPairStillContainsAllEq(ListMap(t), lm, t, h._1, h._2)
        assert(t.forall(p => (ListMap(t) + (h._1, h._2)).contains(p._1)))
        assert(t.forall(p => lm.contains(p._1)))
        assert(Cons(h, t).forall(p => lm.contains(p._1)))
      }
      case Nil() => ()

  }.ensuring(_ => lm.toList.forall(p => lm.contains(p._1)))

  @opaque
  @inlineOnce
  def lemmaInsertPairStillContainsAll[K, B](lm: ListMap[K, B], l: List[(K, B)], k: K, v: B): Unit = {
    require(l.forall(p => lm.contains(p._1)))
    decreases(l)
    l match {
      case Cons(h, t) =>
        if (h._1 != k) {
          TupleListOpsGenK.lemmainsertNoDuplicatedKeysDoesNotModifyOtherKeyValues(lm.toList, k, v, h._1)
        }
        lemmaInsertPairStillContainsAll(lm, t, k, v)
      case Nil() => ()
    }
  }.ensuring(_ => l.forall(p => (lm + (k, v)).contains(p._1)))

  @opaque
  @inlineOnce
  def lemmaInsertPairStillContainsAllEq[K, B](lm: ListMap[K, B], lm2: ListMap[K, B], l: List[(K, B)], k: K, v: B): Unit = {
    require(lm + (k, v) == lm2)
    require(l.forall(p => lm.contains(p._1)))
    decreases(l)
    l match {
      case Cons(h, t) =>
        if (h._1 != k) {
          TupleListOpsGenK.lemmainsertNoDuplicatedKeysDoesNotModifyOtherKeyValues(lm.toList, k, v, h._1)
        }
        lemmaInsertPairStillContainsAllEq(lm, lm2, t, k, v)
      case Nil() => ()
    }
  }.ensuring(_ => l.forall(p => (lm + (k, v)).contains(p._1)) && l.forall(p => (lm2).contains(p._1)))

  @opaque
  @inlineOnce
  def addForallContainsKeyThenBeforeAdding[K, B](
      lm: ListMap[K, B],
      other: ListMap[K, B],
      a: K,
      b: B
  ): Unit = {
    require((lm + (a, b)).toList.forall(p => other.contains(p._1)))
    decreases(lm.toList.size)

    lm.toList match {
      case Cons(head, tl) if (head._1 == a) => ()
      case Cons(head, tl) =>
        addForallContainsKeyThenBeforeAdding(lm.tail, other, a, b)
      case Nil() => ()
    }

  }.ensuring { _ =>
    lm.toList.forall(p => other.contains(p._1))
  }

  @opaque
  @inlineOnce
  def lemmaGetValueImpliesTupleContained[K, B](lm: ListMap[K, B], a: K, b: B): Unit = {
    require(lm.contains(a))
    require(lm.get(a) == Some[B](b))

    TupleListOpsGenK.lemmaGetValueByKeyImpliesContainsTuple(lm.toList, a, b)
  }.ensuring(_ => lm.toList.contains((a, b)))

  @opaque
  def keysOfSound[K, B](@induct lm: ListMap[K, B], value: B): Unit = {
    // trivial by postcondition of getKeysOf
    assert(TupleListOpsGenK.getKeysOf(lm.toList, value).forall(k => lm.get(k) == Some[B](value)))
  }.ensuring(_ => lm.keysOf(value).forall((key: K) => lm.get(key) == Some[B](value)))

  @opaque
  @inlineOnce
  def addNotContainedContent[K, B](
      lm: ListMap[K, B],
      key: K,
      value: B
  ): Unit = {
    require(!lm.contains(key))
    TupleListOpsGenK.lemmainsertNoDuplicatedKeysNotContainedContent(
      lm.toList,
      key,
      value
    )
  }.ensuring(_ =>
    lm.toList.content ++ Set(
      (key, value)
    ) == (lm + (key, value)).toList.content
  )

  // Equivalence LEMMAS ----------------------------------------------------------------------------------------------------------------
  @opaque
  @inlineOnce
  def lemmaAddToEqMapsPreservesEq[K, B](
      lm1: ListMap[K, B],
      lm2: ListMap[K, B],
      key: K,
      value: B
  ): Unit = {
    require(lm1.eq(lm2))
    if (lm1.contains(key)) {
      lemmaAddToEqMapsPreservesEqIfContainsKey(lm1, lm2, key, value)
      assert((lm1 + (key, value)).eq(lm2 + (key, value)))
    } else {
      lemmaAddToEqMapsPreservesEqIfDoesNotContainKey(lm1, lm2, key, value)
      assert((lm1 + (key, value)).eq(lm2 + (key, value)))
    }

  }.ensuring(_ => (lm1 + (key, value)).eq(lm2 + (key, value)))

  @opaque
  @inlineOnce
  def lemmaAddToEqMapsPreservesEqIfDoesNotContainKey[K, B](
      lm1: ListMap[K, B],
      lm2: ListMap[K, B],
      key: K,
      value: B
  ): Unit = {
    require(lm1.eq(lm2))
    require(!lm1.contains(key))
    decreases(lm1.toList.size)

    assert(!lm1.contains(key))
    if (lm2.contains(key)) {
      TupleListOpsGenK.lemmaContainsKeyImpliesGetValueByKeyDefined(lm2.toList, key)
      TupleListOpsGenK.lemmaGetValueByKeyImpliesContainsTuple(lm2.toList, key, lm2.apply(key))
      assert(lm2.toList.contains((key, lm2.apply(key))))
      assert(lm1.toList.contains((key, lm2.apply(key))))
      TupleListOpsGenK.lemmaContainsTupleThenContainsKey(lm1.toList, key, lm2.apply(key))
      assert(false)
    }
    assert(!lm2.contains(key))

    assert((lm1 + (key, value)).eq(lm2 + (key, value)))

  }.ensuring(_ => (lm1 + (key, value)).eq(lm2 + (key, value)))

  @opaque
  @inlineOnce
  def lemmaAddToEqMapsPreservesEqIfContainsKey[K, B](
      lm1: ListMap[K, B],
      lm2: ListMap[K, B],
      key: K,
      value: B
  ): Unit = {
    require(lm1.eq(lm2))
    require(lm1.contains(key))
    decreases(lm1.toList.size)

    lemmaEquivalentThenSameContains(lm1, lm2, key)
    lemmaEquivalentGetSameValue(lm1, lm2, key)

    val v = lm1.apply(key)
    val v2 = lm2.apply(key)
    TupleListOpsGenK.lemmaGetValueByKeyImpliesContainsTuple(lm2.toList, key, v2)
    assert(lm1.toList.contains((key, v)))
    assert(lm2.toList.contains((key, v)))
    assert(lm1.apply(key) == lm2.apply(key))
    assert(lm1.apply(key) == v)

    val lm1WithoutKey = lm1 - key
    val lm2WithoutKey = lm2 - key
    lemmaRemovePreservesEq(lm1, lm2, key)
    assert(lm1WithoutKey.eq(lm2WithoutKey))
    assert(lm1WithoutKey.contains(key) == false)
    assert(lm2WithoutKey.contains(key) == false)

    val lm1After = lm1WithoutKey + (key, value)
    val lm2After = lm2WithoutKey + (key, value)
    lemmaAddToEqMapsPreservesEqIfDoesNotContainKey(lm1WithoutKey, lm2WithoutKey, key, value)

    assert(lm1After.eq(lm2After))

    removeThenAddForSameKeyIsSameAsAdd(lm1, key, value)
    removeThenAddForSameKeyIsSameAsAdd(lm2, key, value)

    assert(lm1After.eq(lm1 + (key, value)))
    assert(lm2After.eq(lm2 + (key, value)))

    assert((lm1 + (key, value)).eq(lm2 + (key, value)))

  }.ensuring(_ => (lm1 + (key, value)).eq(lm2 + (key, value)))

  @opaque
  @inlineOnce
  def lemmaEquivalentThenSameContains[K, B](
      lm1: ListMap[K, B],
      lm2: ListMap[K, B],
      key: K
  ): Unit = {
    require(lm1.eq(lm2))
    if (lm1.contains(key)) {
      val v = lm1.apply(key)
      TupleListOpsGenK.lemmaGetValueByKeyImpliesContainsTuple(lm1.toList, key, v)
      assert(lm1.toList.contains((key, v)))
      assert(lm2.toList.contains((key, v)))
      TupleListOpsGenK.lemmaContainsTupleThenContainsKey(lm2.toList, key, v)

      assert(lm1.contains(key) == true)
      assert(lm2.contains(key) == true)

    } else {
      if (lm2.contains(key)) {
        TupleListOpsGenK.lemmaContainsKeyImpliesGetValueByKeyDefined(lm2.toList, key)
        TupleListOpsGenK.lemmaGetValueByKeyImpliesContainsTuple(lm2.toList, key, lm2.apply(key))
        assert(lm2.toList.contains((key, lm2.apply(key))))
        assert(lm1.toList.contains((key, lm2.apply(key))))
        TupleListOpsGenK.lemmaContainsTupleThenContainsKey(lm1.toList, key, lm2.apply(key))
        assert(false)
      }
      assert(lm1.contains(key) == false)
      assert(lm2.contains(key) == false)
    }
  }.ensuring(_ => lm1.contains(key) == lm2.contains(key))

  @opaque
  @inlineOnce
  def lemmaEquivalentGetSameValue[K, B](
      lm1: ListMap[K, B],
      lm2: ListMap[K, B],
      key: K
  ): Unit = {
    require(lm1.eq(lm2))
    lemmaEquivalentThenSameContains(lm1, lm2, key)
    if (lm1.contains(key)) {
      val v = lm1.apply(key)
      TupleListOpsGenK.lemmaGetValueByKeyImpliesContainsTuple(lm1.toList, key, v)
      assert(lm1.toList.contains((key, v)))
      assert(lm2.toList.contains((key, v)))
      TupleListOpsGenK.lemmaContainsTupleThenContainsKey(lm2.toList, key, v)
      assert(lm2.contains(key))
      val v2 = lm2.apply(key)
      TupleListOpsGenK.lemmaGetValueByKeyImpliesContainsTuple(lm2.toList, key, v2)
      if (v2 != v) {
        assert(lm2.toList.contains((key, v2)))
        assert(lm2.toList.contains((key, v)))
        TupleListOpsGenK.lemmaContainsTwoDifferentTuplesSameKeyImpossible(lm2.toList, key, v, v2)
        assert(false)
      }
      assert(lm1.get(key).get == v)
      assert(lm2.get(key).get == v)
    } else {
      if (lm1.get(key).isDefined) {
        TupleListOpsGenK.lemmaGetValueByKeyImpliesContainsTuple(lm1.toList, key, lm1.get(key).get)
        TupleListOpsGenK.lemmaContainsTupleThenContainsKey(lm1.toList, key, lm1.get(key).get)
        assert(false)
      }
      if (lm2.get(key).isDefined) {
        TupleListOpsGenK.lemmaGetValueByKeyImpliesContainsTuple(lm2.toList, key, lm2.get(key).get)
        TupleListOpsGenK.lemmaContainsTupleThenContainsKey(lm2.toList, key, lm2.get(key).get)
        assert(false)
      }
      assert(lm1.get(key).isEmpty)
      assert(lm2.get(key).isEmpty)
    }

  }.ensuring(_ => lm1.get(key) == lm2.get(key))

  @opaque
  @inlineOnce
  def lemmaRemovePreservesEq[K, B](
      lm1: ListMap[K, B],
      lm2: ListMap[K, B],
      key: K
  ): Unit = {
    require(lm1.eq(lm2))
    lemmaEquivalentThenSameContains(lm1, lm2, key)
    if (lm1.contains(key)) {
      val v = lm1.apply(key)
      val v2 = lm2.apply(key)
      lemmaEquivalentGetSameValue(lm1, lm2, key)
      assert((lm1 - key).toList.content == lm1.toList.content -- Set((key, v)))
      assert((lm2 - key).toList.content == lm2.toList.content -- Set((key, v2)))
    } else {
      assert((lm1 - key).toList.content == lm1.toList.content)
      assert((lm2 - key).toList.content == lm2.toList.content)
    }

  }.ensuring(_ => (lm1 - key).eq(lm2 - key))
}
