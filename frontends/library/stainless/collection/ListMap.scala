/* Copyright 2009-2022 EPFL, Lausanne */

package stainless
package collection

import stainless.annotation._
import stainless.lang._
import StaticChecks._

/** List-backed Map implementation */

@library
case class ListMap[K, B](toList: List[(K, B)]) {
  require(TupleListOpsGenK.invariantList(toList))

  def isEmpty: Boolean = {
    toList.isEmpty
  }.ensuring(res => toList.size >= Int.MaxValue || res == (size == 0))

  def eq(other: ListMap[K, B]): Boolean = toList.content == other.toList.content

  def head: (K, B) = {
    require(!isEmpty)
    toList.head
  }

  def size: Int = {
    require(toList.size < Integer.MAX_VALUE)
    TupleListOpsGenK.intSize(toList)
  }

  @pure
  def nKeys: Int = {
    require(toList.size < Integer.MAX_VALUE)
    TupleListOpsGenK.intSizeKeys(TupleListOpsGenK.getKeysList(toList))
  }

  def tail: ListMap[K, B] = {
    require(!isEmpty)
    ListMap(toList.tail)
  }

  def contains(key: K): Boolean = {
    val res = TupleListOpsGenK.containsKey(toList, key)
    if (res) {
      TupleListOpsGenK.lemmaContainsKeyImpliesGetValueByKeyDefined(toList, key)
      TupleListOpsGenK.lemmaInListThenGetKeysListContains(toList, key)
    } else {
      if (this.keys().contains(key)) {
        TupleListOpsGenK.lemmaInGetKeysListThenContainsKey(toList, key)
        assert(false)
      }
    }
    res

  }.ensuring(res => (!res && !this.keys().contains(key)) || (this.get(key).isDefined && this.keys().contains(key)))

  @inline
  def get(key: K): Option[B] = {
    TupleListOpsGenK.getValueByKey(toList, key)
  }

  @inline
  def keysOf(value: B): List[K] = {
    TupleListOpsGenK.getKeysOf(toList, value)
  }

  def keys(): List[K] = {
    TupleListOpsGenK.getKeysList(toList)
  }.ensuring(res =>
    ListSpecs.noDuplicate(res)
      && res.length == this.toList.length
      && res.forall(k => TupleListOpsGenK.containsKey(this.toList, k))
      && res.content == this.toList.map(_._1).content
  )

  def apply(key: K): B = {
    require(contains(key))
    get(key).get
  }

  def +(keyValue: (K, B)): ListMap[K, B] = {
    val newList =
      TupleListOpsGenK.insertNoDuplicatedKeys(toList, keyValue._1, keyValue._2)

    TupleListOpsGenK.lemmaContainsTupThenGetReturnValue(
      newList,
      keyValue._1,
      keyValue._2
    )
    ListMap(newList)

  }.ensuring(res =>
    res.contains(keyValue._1) && res.get(keyValue._1) == Some[B](
      keyValue._2
    ) && res.toList.contains(keyValue)
  )

  def ++(keyValues: List[(K, B)]): ListMap[K, B] = {
    decreases(keyValues)
    keyValues match {
      case Nil()                => this
      case Cons(keyValue, rest) => (this + keyValue) ++ rest
    }
  }
  def -(key: K): ListMap[K, B] = {
    ListMap(TupleListOpsGenK.removePresrvNoDuplicatedKeys(toList, key))
  }.ensuring(res =>
    !res.contains(key)
      && this.keys().content - key == res.keys().content
  )

  def --(keys: List[K]): ListMap[K, B] = {
    decreases(keys)
    keys match {
      case Nil()           => this
      case Cons(key, rest) => (this - key) -- rest
    }
  }
  @inline
  def forall(p: ((K, B)) => Boolean): Boolean = {
    toList.forall(p)
  }
}

@library
object ListMap {
  @library
  def empty[A, B]: ListMap[A, B] = ListMap(List.empty[(A, B)])

  @library
  def fromList[K, V](l: List[(K, V)]): ListMap[K, V] = l.foldLeft(ListMap.empty[K, V]) {
    case (current, (k, v)) => current + (k -> v)
  }

  @library
  implicit class ToListMapOps[K, V](l: List[(K, V)]) {
    def toListMap: ListMap[K, V] = fromList(l)
  }
}

@library
object TupleListOpsGenK {

  // @inline
  def invariantList[K, B](l: List[(K, B)]): Boolean = {
    noDuplicatedKeys(l)
  }

  def getKeysList[K, B](l: List[(K, B)]): List[K] = {
    require(invariantList(l))
    decreases(l)
    l match {
      case Cons(head, tl) =>
        if (containsKey(tl, head._1)) {
          assert(false)
        }
        if (getKeysList(tl).contains(head._1)) {
          ListSpecs.forallContained(getKeysList(tl), k => containsKey(tl, k), head._1)
          assert(false)
        }
        assert(ListSpecs.noDuplicate(getKeysList(tl)) && getKeysList(tl).forall(k => containsKey(tl, k)))
        assert(ListSpecs.noDuplicate(Cons(head._1, getKeysList(tl))))
        assert(getKeysList(tl).forall(k => containsKey(tl, k)))
        lemmaForallContainsAddHeadPreserves(tl, getKeysList(tl), head)
        assert(getKeysList(tl).forall(k => containsKey(Cons(head, tl), k)))
        assert(Cons(head._1, getKeysList(tl)).forall(k => containsKey(Cons(head, tl), k)))
        Cons(head._1, getKeysList(tl))
      case Nil() => Nil[K]()
    }
  }.ensuring(res =>
    ListSpecs.noDuplicate(res)
      && res.length == l.length
      && res.forall(k => containsKey(l, k))
      && res.content == l.map(_._1).content
  )

  @pure
  def intSizeKeys[K](l: List[K]): Int = {
    require(l.length < Integer.MAX_VALUE)
    decreases(l)

    l match {
      case Cons(head, tl) => 1 + intSizeKeys(tl)
      case Nil()          => 0
    }
  }

  def intSize[K, B](l: List[(K, B)]): Int = {
    decreases(l)
    l match {
      case Cons(head, tl) => {
        val s1 = intSize(tl)
        if (s1 < Integer.MAX_VALUE) {
          1 + s1
        } else {
          Integer.MAX_VALUE
        }
      }

      case Nil() => 0
    }
  }.ensuring(res => res >= 0 && (l.isEmpty == (res == 0)))

  def getKeysOf[K, B](l: List[(K, B)], value: B): List[K] = {
    require(invariantList(l))
    decreases(l)

    l match {
      case Cons(head, tl) if (head._2 == value) => {
        if (!getKeysOf(tl, value).isEmpty) {
          lemmaForallGetValueByKeySameWithADiffHead(
            tl,
            getKeysOf(tl, value),
            value,
            head
          )

        }
        Cons(head._1, getKeysOf(tl, value))
      }
      case Cons(head, tl) if (head._2 != value) => {
        val r = getKeysOf(tl, value)
        if (!getKeysOf(tl, value).isEmpty) {
          lemmaForallGetValueByKeySameWithADiffHead(
            tl,
            getKeysOf(tl, value),
            value,
            head
          )
        }
        getKeysOf(tl, value)
      }
      case Nil() => Nil[K]()
    }

  }.ensuring(res => res.forall(getValueByKey(l, _) == Some[B](value)))

  def filterByValue[K, B](l: List[(K, B)], value: B): List[(K, B)] = {
    require(invariantList(l))
    decreases(l)

    l match {
      case Cons(head, tl) if (head._2 == value) =>
        val res = head :: filterByValue(tl, value)
        if (containsKey(filterByValue(tl, value), head._1)) {
          assert(ListSpecs.subseq(filterByValue(tl, value), tl))
          lemmaContainsKeyImpliesGetValueByKeyDefined(filterByValue(tl, value), head._1)
          val va = getValueByKey(filterByValue(tl, value), head._1).get
          lemmaGetValueByKeyImpliesContainsTuple(filterByValue(tl, value), head._1, va)
          ListSpecs.subseqContains(filterByValue(tl, value), tl, (head._1, va))
          assert(tl.contains((head._1, va)))
          lemmaContainsTupleThenContainsKey(tl, head._1, va)
          assert(containsKey(tl, head._1))
          assert(false)
        }
        assert(!containsKey(filterByValue(tl, value), head._1))
        res
      case Cons(head, tl) if (head._2 != value) =>
        val res = filterByValue(tl, value)
        res
      case Nil() => Nil[(K, B)]()
    }
  }.ensuring(res => res.forall(_._2 == value) && ListSpecs.subseq(res, l) && invariantList(res))

  def getValueByKey[K, B](l: List[(K, B)], key: K): Option[B] = {
    require(invariantList(l))
    decreases(l)

    l match {
      case Cons(head, tl) if (head._1 == key) => Some[B](head._2)
      case Cons(head, tl) if (head._1 != key) => getValueByKey(tl, key)
      case Nil()                              => None[B]()
    }

  }

  def insertNoDuplicatedKeys[K, B](
      l: List[(K, B)],
      newKey: K,
      newValue: B
  ): List[(K, B)] = {
    require(invariantList(l))
    decreases(l)

    l match {
      case Cons(head, tl) if (head._1 == newKey) =>
        lemmaSubseqRefl(getKeysList(l))
        (newKey, newValue) :: tl
      case Cons(head, tl) if (!containsKey(l, newKey)) => (newKey, newValue) :: l
      case Cons(head, tl) =>
        assert(containsKey(tl, newKey))
        val res = head :: insertNoDuplicatedKeys(tl, newKey, newValue)
        if (containsKey(insertNoDuplicatedKeys(tl, newKey, newValue), head._1)) {
          assert(head._1 != newKey)
          assert(getKeysList(tl).content ++ Set(newKey) == getKeysList(insertNoDuplicatedKeys(tl, newKey, newValue)).content)
          lemmaInListThenGetKeysListContains(insertNoDuplicatedKeys(tl, newKey, newValue), head._1)
          assert(getKeysList(insertNoDuplicatedKeys(tl, newKey, newValue)).contains(head._1))
          assert(getKeysList(tl).contains(head._1))
          lemmaInGetKeysListThenContainsKey(tl, head._1)
          assert(containsKey(tl, head._1))
          assert(false)
        }
        assert(invariantList(res))
        assert(containsKey(res, newKey))
        assert(res.contains((newKey, newValue)))
        res
      case Nil() => (newKey, newValue) :: Nil()
    }
  }.ensuring(res =>
    invariantList(res) && containsKey(res, newKey) &&
      res.contains((newKey, newValue)) &&
      getKeysList(res).content == getKeysList(l).content ++ Set(newKey)
  )

  def removePresrvNoDuplicatedKeys[K, B](
      l: List[(K, B)],
      key: K
  ): List[(K, B)] = {
    require(invariantList(l))
    decreases(l)
    l match {
      case Cons(head, tl) if (head._1 == key) =>
        if (containsKey(l, key)) {
          val h = (key, getValueByKey(l, key).get)
          assert(l.head == (key, getValueByKey(l, key).get))
          if (tl.contains(h)) {
            lemmaContainsTupleThenContainsKey(tl, h._1, h._2)
            assert(false)
          }
          assert(!tl.contains(head))
          assert(tl.content == l.content - (key, getValueByKey(l, key).get))
        } else {
          assert(tl.content == l.content)
        }
        tl
      case Cons(head, tl) if (head._1 != key) =>
        val res = head :: removePresrvNoDuplicatedKeys(tl, key)
        if (getKeysList(tl).contains(head._1)) {
          lemmaInGetKeysListThenContainsKey(tl, head._1)
          assert(false)
        }
        if (containsKey(removePresrvNoDuplicatedKeys(tl, key), head._1)) {
          lemmaInListThenGetKeysListContains(removePresrvNoDuplicatedKeys(tl, key), head._1)
          assert(false)
        }
        res
      case Nil() => Nil[(K, B)]()
    }
  }.ensuring(res =>
    invariantList(res) &&
      !containsKey(res, key) &&
      getKeysList(res).content == getKeysList(l).content -- Set(key) &&
      (if (containsKey(l, key)) {
         lemmaContainsKeyImpliesGetValueByKeyDefined(l, key)
         res.content == l.content - (key, getValueByKey(l, key).get)
       } else {
         res.content == l.content
       })
  )

  def noDuplicatedKeys[K, B](l: List[(K, B)]): Boolean = {
    decreases(l)
    l match {
      case Nil()                                  => true
      case Cons(_, Nil())                         => true
      case Cons(h1, t) if (containsKey(t, h1._1)) => false
      case Cons(_, t)                             => noDuplicatedKeys(t)
    }
  }

  def containsKey[K, B](l: List[(K, B)], key: K): Boolean = {
    decreases(l)
    l match {
      case Cons(head, _) if (head._1 == key) => true
      case Cons(_, tl)                       => containsKey(tl, key)
      case Nil()                             => false

    }
  }

  // ----------- LEMMAS -----------------------------------------------------

  @opaque
  @inlineOnce
  def lemmaRemoveFromListThenKeysSetRemove[K, B](l: List[(K, B)], key: K): Unit = {
    require(invariantList(l))
    decreases(l)
    l match {
      case Cons(head, tl) if (head._1 == key) =>
        if (containsKey(l, key)) {
          val h = (key, getValueByKey(l, key).get)
          assert(l.head == (key, getValueByKey(l, key).get))
          if (tl.contains(h)) {
            lemmaContainsTupleThenContainsKey(tl, h._1, h._2)
            assert(false)
          }
          assert(!tl.contains(head))
          assert(tl.content == l.content - (key, getValueByKey(l, key).get))
        } else {
          assert(tl.content == l.content)
        }
      case Cons(head, tl) if (head._1 != key) =>
        lemmaRemoveFromListThenKeysSetRemove(tl, key)
        if (getKeysList(tl).contains(head._1)) {
          lemmaInGetKeysListThenContainsKey(tl, head._1)
          assert(false)
        }
        if (containsKey(removePresrvNoDuplicatedKeys(tl, key), head._1)) {
          lemmaInListThenGetKeysListContains(removePresrvNoDuplicatedKeys(tl, key), head._1)
          assert(false)
        }
      case Nil() => ()
    }
  }.ensuring(_ => getKeysList(l).content - key == getKeysList(removePresrvNoDuplicatedKeys(l, key)).content)

  @opaque
  @inlineOnce
  def lemmaEqMapSameKeysSet[K, B](lm1: ListMap[K, B], lm2: ListMap[K, B]): Unit = {
    require(lm1.eq(lm2))
    assert(lm1.toList.content == lm2.toList.content)
    ListSpecs.subsetRefl(lm1.toList)
    ListSpecs.subsetRefl(lm2.toList)
    lemmaSubsetThenKeysSubset(lm1.toList, lm2.toList)
    lemmaSubsetThenKeysSubset(lm2.toList, lm1.toList)
    assert(lm1.keys().content.subsetOf(lm2.keys().content))
    assert(lm2.keys().content.subsetOf(lm1.keys().content))
  }.ensuring(_ => lm1.keys().content == lm2.keys().content)

  @opaque
  @inlineOnce
  def lemmaSubsetThenKeysSubset[K, B](l1: List[(K, B)], l2: List[(K, B)]): Unit = {
    require(invariantList(l1))
    require(invariantList(l2))
    require(l1.content.subsetOf(l2.content))
    decreases(l1)
    l1 match
      case Cons(hd, tl) =>
        lemmaSubsetThenKeysSubset(tl, l2)
        assert(getKeysList(tl).content.subsetOf(getKeysList(l2).content))
        assert(l2.contains(hd))
        lemmaMapFirstElmtContains(l2, hd)
        assert(l2.map(_._1).contains(hd._1))
        assert(getKeysList(l2).contains(hd._1))
        assert(!containsKey(tl, hd._1))
        if (getKeysList(tl).contains(hd._1)) {
          lemmaInGetKeysListThenContainsKey(tl, hd._1)
          assert(false)
        }
        assert(!getKeysList(tl).contains(hd._1))
      case Nil() => ()

  }.ensuring(_ => getKeysList(l1).content.subsetOf(getKeysList(l2).content))

  @opaque
  @inlineOnce
  def lemmaMapFirstElmtContains[K, B](l: List[(K, B)], p: (K, B)): Unit = {
    require(invariantList(l))
    require(l.contains(p))
    decreases(l)
    l match {
      case Cons(head, tl) if (head != p) =>
        lemmaMapFirstElmtContains(tl, p)
      case _ => ()
    }
  }.ensuring(_ => l.map(_._1).contains(p._1))

  @opaque
  @inlineOnce
  def lemmaForallSubset[K, B](
      l1: List[(K, B)],
      l2: List[(K, B)],
      p: ((K, B)) => Boolean
  ): Unit = {
    require(invariantList(l1))
    require(invariantList(l2))
    require(l2.forall(p) && l1.content.subsetOf(l2.content))
    decreases(l1)

    l1 match {
      case Cons(head, tl) =>
        ListSpecs.subsetContains(l1, l2)
        ListSpecs.forallContained(l1, l2.contains, head)
        ListSpecs.forallContained(l2, p, head)
        assert(l2.contains(head))
        lemmaForallSubset(tl, l2, p)
        assert(tl.forall(p))
        assert(p(head))
      case Nil() => ()
    }
  }.ensuring(_ => l1.forall(p))

  @opaque
  @inlineOnce
  def lemmaInsertNoDuplicatedKeysPreservesForall[K, B](
      l: List[(K, B)],
      key: K,
      value: B,
      p: ((K, B)) => Boolean
  ): Unit = {
    require(invariantList(l))
    require(l.forall(p))
    require(p((key, value)))
    decreases(l)

    l match {
      case Cons(head, tl) if (head._1 != key) =>
        lemmaInsertNoDuplicatedKeysPreservesForall(tl, key, value, p)
      case _ => ()
    }

  }.ensuring(_ => insertNoDuplicatedKeys(l, key, value).forall(p))

  @opaque
  @inlineOnce
  def lemmaContainsTwoDifferentTuplesSameKeyImpossible[K, B](
      l: List[(K, B)],
      key: K,
      v1: B,
      v2: B
  ): Unit = {
    require(l.contains((key, v1)) && l.contains((key, v2)))
    require(invariantList(l))
    decreases(l)

    l match {
      case Cons(head, tl) if (head._1 != key) =>
        lemmaContainsTwoDifferentTuplesSameKeyImpossible(tl, key, v1, v2)
      case Cons(head, tl) if (head._1 == key) =>
        if (head._2 == v1) {
          if (v1 != v2) {
            lemmaContainsTupleThenContainsKey(tl, key, v2)
            assert(false)
          }
        } else {
          if (head._2 != v2) {
            lemmaContainsTupleThenContainsKey(tl, key, v2)
            lemmaContainsTupleThenContainsKey(tl, key, v1)
            assert(false)
          }
          assert(head._2 == v2)
          if (v1 != v2) {
            lemmaContainsTupleThenContainsKey(tl, key, v1)
            assert(false)
          }
        }
      case _ => ()
    }
  }.ensuring(_ => v1 == v2)

  @opaque
  @inlineOnce
  def lemmaInListThenGetKeysListContains[K, B](l: List[(K, B)], key: K): Unit = {
    require(invariantList(l))
    require(containsKey(l, key))
    decreases(l)

    l match {
      case Cons(head, tl) if (head._1 != key) =>
        lemmaInListThenGetKeysListContains(tl, key)
      case _ => ()
    }
  }.ensuring(_ => getKeysList(l).contains(key))

  @inlineOnce
  @opaque
  def lemmaInGetKeysListThenContainsKey[K, B](l: List[(K, B)], key: K): Unit = {
    require(invariantList(l))
    require(getKeysList(l).contains(key))
    decreases(l)

    l match {
      case Cons(head, tl) if (head._1 != key) =>
        lemmaInGetKeysListThenContainsKey(tl, key)
      case _ => ()
    }
  }.ensuring(_ => containsKey(l, key))

  @inlineOnce
  @opaque
  def lemmaSubseqRefl[B](l: List[B]): Unit = {
    decreases(l.size)
    l match {
      case Nil()        => ()
      case Cons(hd, tl) => lemmaSubseqRefl(tl)
    }
  }.ensuring(_ => ListSpecs.subseq(l, l))

  @opaque
  @inlineOnce
  def lemmaForallContainsAddHeadPreserves[K, B](l: List[(K, B)], keys: List[K], other: (K, B)): Unit = {
    require(invariantList(l))
    require(keys.forall(k => containsKey(l, k)))
    require(!containsKey(l, other._1))
    decreases(keys)

    keys match {
      case Cons(head, tl) => {
        lemmaAddHeadStillContainsKey(l, other._1, other._2, head)
        lemmaForallContainsAddHeadPreserves(l, tl, other)
      }
      case _ => ()
    }

  }.ensuring(_ => keys.forall(k => containsKey(Cons(other, l), k)))

  @opaque
  @inlineOnce
  def lemmaGetValueByKeyImpliesContainsTuple[K, B](l: List[(K, B)], key: K, v: B): Unit = {
    require(invariantList(l))
    require(getValueByKey(l, key) == Some[B](v))
    decreases(l)
    l match {
      case Cons(head, tl) if (head._1 != key) =>
        lemmaGetValueByKeyImpliesContainsTuple(tl, key, v)
      case _ => ()
    }
  }.ensuring(_ => l.contains((key, v)))

  @opaque
  @inlineOnce
  def lemmaInsertAndremovePresrvNoDuplicatedKeysCommutative[K, B](
      l: List[(K, B)],
      key1: K,
      v1: B,
      key2: K
  ): Unit = {
    require(key1 != key2)
    require(invariantList(l))
    decreases(l)

    l match {
      case Cons(head, tl) => {
        lemmaInsertAndremovePresrvNoDuplicatedKeysCommutative(tl, key1, v1, key2)
      }
      case _ => ()
    }

  }.ensuring(_ =>
    insertNoDuplicatedKeys(
      removePresrvNoDuplicatedKeys(l, key2),
      key1,
      v1
    ) == removePresrvNoDuplicatedKeys(
      insertNoDuplicatedKeys(l, key1, v1),
      key2
    )
  )

  @opaque
  @inlineOnce
  def lemmainsertNoDuplicatedKeysThenRemoveIsSame[K, B](
      l: List[(K, B)],
      key1: K,
      v1: B
  ): Unit = {
    require(invariantList(l))
    require(!containsKey(l, key1))
    decreases(l)

    l match {
      case Cons(head, tl) => {
        lemmaTailStillNotContainsKey(l, key1)
        lemmainsertNoDuplicatedKeysThenRemoveIsSame(tl, key1, v1)
      }
      case _ => ()
    }

  }.ensuring(_ => removePresrvNoDuplicatedKeys(insertNoDuplicatedKeys(l, key1, v1), key1) == l)

  @opaque
  @inlineOnce
  def lemmaRemoveTheninsertNoDuplicatedKeysIsSameAsInsert[K, B](
      l: List[(K, B)],
      key1: K,
      v1: B
  ): Unit = {
    require(invariantList(l))
    decreases(l)

    l match {
      case Cons(head, tl) if (head._1 == key1) => ()
      case Cons(head, tl) => {
        lemmaRemoveTheninsertNoDuplicatedKeysIsSameAsInsert(tl, key1, v1)
      }
      case _ => ()
    }

  }.ensuring(_ => insertNoDuplicatedKeys(removePresrvNoDuplicatedKeys(l, key1), key1, v1).content == insertNoDuplicatedKeys(l, key1, v1).content)

  @opaque
  @inlineOnce
  def lemmainsertNoDuplicatedKeysCommutative[K, B](
      l: List[(K, B)],
      key1: K,
      v1: B,
      key2: K,
      v2: B
  ): Unit = {
    require(key1 != key2)
    require(invariantList(l))
    decreases(l)

    l match {
      case Cons(head, tl) if (head._1 == key1) => ()
      case Cons(head, tl) => {
        lemmainsertNoDuplicatedKeysCommutative(tl, key1, v1, key2, v2)
      }
      case _ => ()
    }

  }.ensuring(_ =>
    insertNoDuplicatedKeys(
      insertNoDuplicatedKeys(l, key1, v1),
      key2,
      v2
    ).content == insertNoDuplicatedKeys(
      insertNoDuplicatedKeys(l, key2, v2),
      key1,
      v1
    ).content
  )

  @opaque
  @inlineOnce
  def lemmaremovePresrvNoDuplicatedKeysCommutative[K, B](
      l: List[(K, B)],
      key1: K,
      key2: K
  ): Unit = {
    require(invariantList(l))
    decreases(l)

    l match {
      case Cons(head, tl) => {
        lemmaremovePresrvNoDuplicatedKeysCommutative(tl, key1, key2)
      }
      case _ => ()
    }

  }.ensuring(_ =>
    removePresrvNoDuplicatedKeys(
      removePresrvNoDuplicatedKeys(l, key1),
      key2
    ) == removePresrvNoDuplicatedKeys(
      removePresrvNoDuplicatedKeys(l, key2),
      key1
    )
  )

  @opaque
  @inlineOnce
  def lemmaremovePresrvNoDuplicatedKeysNotPresentPreserves[K, B](
      l: List[(K, B)],
      key: K
  ): Unit = {
    require(invariantList(l))
    require(!containsKey(l, key))
    decreases(l)

    l match {
      case Cons(head, tl) => {
        lemmaTailStillNotContainsKey(l, key)
        assert(!containsKey(tl, key))
        lemmaremovePresrvNoDuplicatedKeysNotPresentPreserves(tl, key)
      }
      case _ => ()
    }

  }.ensuring(_ => removePresrvNoDuplicatedKeys(l, key) == l)

  @opaque
  @inlineOnce
  def lemmainsertNoDuplicatedKeysErasesIfSameKey[K, B](
      l: List[(K, B)],
      key1: K,
      v1: B,
      v2: B
  ): Unit = {
    require(invariantList(l))
    decreases(l)

    l match {
      case Cons(head, tl) => {
        lemmainsertNoDuplicatedKeysErasesIfSameKey(tl, key1, v1, v2)
      }
      case _ => ()
    }

  }.ensuring(_ =>
    insertNoDuplicatedKeys(
      insertNoDuplicatedKeys(l, key1, v1),
      key1,
      v2
    ) == insertNoDuplicatedKeys(
      l,
      key1,
      v2
    )
  )

  @opaque
  @inlineOnce
  def lemmaAddNewKeyIncrementSize[K, B](
      l: List[(K, B)],
      key: K,
      value: B
  ): Unit = {
    require(invariantList(l))
    require(!containsKey(l, key))
    decreases(l)

    val inserted = insertNoDuplicatedKeys(l, key, value)
    l match {
      case Cons(head, tl) if (head._1 != key) => {
        lemmaAddNewKeyIncrementSize(tl, key, value)

      }
      case Cons(head, tl) if (head._1 == key) => assert(false)
      case _                                  =>
    }

  }.ensuring(_ => insertNoDuplicatedKeys(l, key, value).length == l.length + 1)

  @opaque
  @inlineOnce
  def lemmaAddExistingKeyPreservesSize[K, B](
      l: List[(K, B)],
      key: K,
      value: B
  ): Unit = {
    decreases(l)
    require(invariantList(l))
    require(containsKey(l, key))

    val inserted = insertNoDuplicatedKeys(l, key, value)
    l match {
      case Cons(head, tl) if (head._1 != key) => {
        lemmaAddExistingKeyPreservesSize(tl, key, value)
      }
      case Cons(head, tl) if (head._1 == key) => {
        assert(inserted == Cons((key, value), tl))
      }
      case _ =>
    }

  }.ensuring(_ => insertNoDuplicatedKeys(l, key, value).length == l.length)

  @opaque
  @inlineOnce
  def lemmaGetValueByKeyIsDefinedImpliesContainsKey[K, B](
      l: List[(K, B)],
      key: K
  ): Unit = {
    require(invariantList(l) && getValueByKey(l, key).isDefined)
    decreases(l)
    l match {
      case Cons(head, tl) if (head._1 != key) =>
        lemmaGetValueByKeyIsDefinedImpliesContainsKey(tl, key)
        lemmaAddHeadStillContainsKey(tl, head._1, head._2, key)
      case _ => ()
    }
  }.ensuring(_ => containsKey(l, key))

  @opaque
  @inlineOnce
  def lemmaContainsKeyImpliesGetValueByKeyDefined[K, B](
      l: List[(K, B)],
      key: K
  ): Unit = {
    require(invariantList(l))
    require(containsKey(l, key))
    decreases(l)
    l match {
      case Cons(head, tl) if (head._1 != key) =>
        lemmaContainsKeyImpliesGetValueByKeyDefined(tl, key)
      case _ => ()
    }
  }.ensuring(_ => getValueByKey(l, key).isDefined)

  @opaque
  @inlineOnce
  def lemmaForallGetValueByKeySameWithADiffHead[K, B](
      l: List[(K, B)],
      keys: List[K],
      value: B,
      newHead: (K, B)
  ): Unit = {
    require(invariantList(l))
    require(!l.isEmpty)
    require(keys.forall(getValueByKey(l, _) == Some[B](value)))
    require(!containsKey(l, newHead._1))
    decreases(keys)

    keys match {
      case Cons(head, tl) => {
        lemmaGetValueByKeyIsDefinedImpliesContainsKey(l, head)
        lemmaAddHeadStillContainsKey(l, newHead._1, newHead._2, head)
        lemmaContainsKeyImpliesGetValueByKeyDefined(Cons(newHead, l), head)
        lemmaForallGetValueByKeySameWithADiffHead(l, tl, value, newHead)
      }
      case _ => ()
    }

  }.ensuring(_ => keys.forall(k => getValueByKey(Cons(newHead, l), k) == Some[B](value)))

  @opaque
  @inlineOnce
  def lemmaAddHeadStillContainsKey[K, B](
      l: List[(K, B)],
      key: K,
      value: B,
      test: K
  ): Unit = {
    require(invariantList(l))
    require(containsKey(l, test))
    require(!containsKey(l, key))
    decreases(l)

    l match {
      case Cons(head, tl) if (head._1 != test) =>
        lemmaAddHeadStillContainsKey(tl, key, value, test)
      case _ => ()
    }

  }.ensuring(_ => containsKey(Cons((key, value), l), test))

  @opaque
  @inlineOnce
  def lemmaTailStillNotContainsKey[K, B](
      l: List[(K, B)],
      test: K
  ): Unit = {
    require(invariantList(l))
    require(!containsKey(l, test))
    require(!l.isEmpty)
    decreases(l)

    l match {
      case Cons(head, Nil()) => ()
      case Cons(head, tl) if (head._1 != test) =>
        if (containsKey(tl, test)) {
          lemmaAddHeadStillContainsKey(tl, head._1, head._2, test)
          assert(false)
        }
        lemmaTailStillNotContainsKey(tl, test)
      case _ => ()
    }

  }.ensuring(_ => !containsKey(l.tail, test))

  @opaque
  @inlineOnce
  def lemmainsertNoDuplicatedKeysDoesNotModifyOtherKeyValues[K, B](
      l: List[(K, B)],
      newKey: K,
      newValue: B,
      otherKey: K
  ): Unit = {
    require(invariantList(l) && newKey != otherKey)
    decreases(l)

    l match {
      case Cons(head, tl) if (head._1 != otherKey) =>
        lemmainsertNoDuplicatedKeysDoesNotModifyOtherKeyValues(
          tl,
          newKey,
          newValue,
          otherKey
        )
      case _ => ()
    }

  }.ensuring(_ =>
    containsKey(
      insertNoDuplicatedKeys(l, newKey, newValue),
      otherKey
    ) == containsKey(l, otherKey) &&
      getValueByKey(
        insertNoDuplicatedKeys(l, newKey, newValue),
        otherKey
      ) == getValueByKey(
        l,
        otherKey
      )
  )

  @opaque
  @inlineOnce
  def lemmainsertNoDuplicatedKeysDoesNotModifyOtherKeysNotContained[K, B](
      l: List[(K, B)],
      newKey: K,
      newValue: B,
      otherKey: K
  ): Unit = {
    require(invariantList(l))
    require(!containsKey(l, otherKey))
    require(otherKey != newKey)
    decreases(l)

    l match {
      case Cons(head, tl) =>
        lemmaTailStillNotContainsKey(l, otherKey)
        assert(!containsKey(tl, otherKey))
        lemmainsertNoDuplicatedKeysDoesNotModifyOtherKeysNotContained(
          tl,
          newKey,
          newValue,
          otherKey
        )
      case _ => ()
    }
  }.ensuring(_ => !containsKey(insertNoDuplicatedKeys(l, newKey, newValue), otherKey))

  @opaque
  @inlineOnce
  def lemmainsertNoDuplicatedKeysDoesNotModifyOtherKeysContained[K, B](
      l: List[(K, B)],
      newKey: K,
      newValue: B,
      otherKey: K
  ): Unit = {
    require(invariantList(l) && containsKey(l, otherKey) && otherKey != newKey)
    decreases(l)

    l match {
      case Cons(head, tl) if (head._1 != otherKey) =>
        lemmainsertNoDuplicatedKeysDoesNotModifyOtherKeysContained(
          tl,
          newKey,
          newValue,
          otherKey
        )
      case _ => ()
    }
  }.ensuring(_ => containsKey(insertNoDuplicatedKeys(l, newKey, newValue), otherKey))

  @opaque
  @inlineOnce
  def lemmainsertNoDuplicatedKeysNotContainedContent[K, B](
      l: List[(K, B)],
      newKey: K,
      newValue: B
  ): Unit = {
    require(invariantList(l))
    require(!containsKey(l, newKey))
    decreases(l)

    l match {
      case Cons(head, tl) => {
        lemmaTailStillNotContainsKey(l, newKey)
        lemmainsertNoDuplicatedKeysNotContainedContent(tl, newKey, newValue)
      }
      case _ => ()
    }

  }.ensuring(_ =>
    l.content ++ Set((newKey, newValue)) == insertNoDuplicatedKeys(
      l,
      newKey,
      newValue
    ).content
  )

  @opaque
  @inlineOnce
  def lemmaNotContainsKeyThenNotContainsTuple[K, B](
      l: List[(K, B)],
      key: K,
      value: B
  ): Unit = {
    require(invariantList(l))
    require(!containsKey(l, key))
    decreases(l)
    l match {
      case Cons(head, tl) =>
        lemmaTailStillNotContainsKey(l, key)
        lemmaNotContainsKeyThenNotContainsTuple(tl, key, value)
      case _ => ()
    }

  }.ensuring(_ => !l.contains((key, value)))

  @opaque
  @inlineOnce
  def lemmaContainsTupleThenContainsKey[K, B](
      l: List[(K, B)],
      key: K,
      value: B
  ): Unit = {
    require(invariantList(l))
    require(l.contains((key, value)))
    decreases(l)

    l match {
      case Cons(head, tl) if (head != (key, value)) =>
        lemmaContainsTupleThenContainsKey(tl, key, value)
      case _ => ()
    }
  }.ensuring(_ => containsKey(l, key))

  @opaque
  @inlineOnce
  def lemmaContainsTupThenGetReturnValue[K, B](
      l: List[(K, B)],
      key: K,
      value: B
  ): Unit = {
    require(invariantList(l) && containsKey(l, key) && l.contains((key, value)))
    decreases(l)

    l match {
      case head :: Nil() => ()
      case Cons(head, tl) if (head._1 == key) =>
        lemmaNotContainsKeyThenNotContainsTuple(tl, key, value)
      case Cons(head, tl) => lemmaContainsTupThenGetReturnValue(tl, key, value)
      case Nil()          => ()
    }
  }.ensuring(_ => getValueByKey(l, key) == Some[B](value))
}
