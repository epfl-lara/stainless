package stainless.wasm

import stainless.lang._
import stainless.annotation.library

/** Implements tuples,
  * as well as set, map and bag operations on top of sorted lists
  */
@library
object Runtime {

  sealed case class _Tuple2_[T1, T2](e1: T1, e2: T2)
  sealed case class _Tuple3_[T1, T2, T3](e1: T1, e2: T2, e3: T3)
  sealed case class _Tuple4_[T1, T2, T3, T4](e1: T1, e2: T2, e3: T3, e4: T4)

  /* Transforms any type to a string.  Will be filled in by the code generator */
  @library
  def _toString_[A](a: A): String = ""

  /* String transformers for basic types */
	@library
  def _digitToStringL_(b: Long): String = {
    b match {
      case _ if b == 0 => "0"
      case _ if b == 1 => "1"
      case _ if b == 2 => "2"
      case _ if b == 3 => "3"
      case _ if b == 4 => "4"
      case _ if b == 5 => "5"
      case _ if b == 6 => "6"
      case _ if b == 7 => "7"
      case _ if b == 8 => "8"
      case _ if b == 9 => "9"
    }
  }

  @library
  def _digitToStringI_(b: Int): String = {
    b match {
      case _ if b == 0 => "0"
      case _ if b == 1 => "1"
      case _ if b == 2 => "2"
      case _ if b == 3 => "3"
      case _ if b == 4 => "4"
      case _ if b == 5 => "5"
      case _ if b == 6 => "6"
      case _ if b == 7 => "7"
      case _ if b == 8 => "8"
      case _ if b == 9 => "9"
    }
  }

	@library
  def _i64ToString_(b: Long): String = {
    if (b < 0) "-" + _i64ToString_(-b)
    else if (b <= 9) _digitToStringL_(b)
    else _i64ToString_(b / 10) + _digitToStringL_(b % 10)
  }

	@library
  def _i32ToString_(b: Int): String = {
    if (b < 0) "-" + _i32ToString_(-b)
    else if (b <= 9) _digitToStringI_(b)
    else _i32ToString_(b / 10) + _digitToStringI_(b % 10)
  }


	@library
	def _booleanToString_(i: Int) = if (i == 0) "false" else "true"
	@library // TODO
	def _f64ToString_(b: Real): String = "<real>"
	@library
	def _funToString_(): String = "<function>"

  /* compares two elements of any type. Will be filled in by the code generator */
  @library
  def _compare_[A](a1: A, a2: A): Int = 0

  // We define our own lists to not have to load the entire scala lib
  @library
  sealed abstract class _Set_[A] {
    @inline def ::(elem: A): _Set_[A] = _SCons_(elem, this)
  }
  @library
  case class _SCons_[A](h: A, t: _Set_[A]) extends _Set_[A]
  @library
  case class _SNil_[A]() extends _Set_[A]

  @library
  def __SNil_$0ToString_[A](s: _Set_[A]) = "Set()"
  @library
  def __SCons_$0ToString_[A](s: _Set_[A]) = {
    def rec(s: _Set_[A]): String = s match {
      case _SCons_(e1, s1@ _SCons_(_, _)) => _toString_[A](e1) + ", " + rec(s1)
      case _SCons_(e1, _SNil_()) => _toString_[A](e1)
    }
    "Set(" + rec(s) + ")"
  }

  @library
  def _setAdd_[A](set: _Set_[A], elem: A): _Set_[A] = set match {
    case _SNil_() => elem :: _SNil_()
    case _SCons_(h, t) =>
      val c = _compare_(elem, h)
      if (c < 0) elem :: h :: t
      else if (c > 0) h :: _setAdd_(t, elem)
      else h :: t
  }
  @library
  def _elementOfSet_[A](set: _Set_[A], elem: A): Boolean = set match {
    case _SNil_() => false
    case _SCons_(h, t) =>
      val c = _compare_(elem, h)
      if (c < 0) false
      else if (c > 0) _elementOfSet_(t, elem)
      else true
  }
  @library
  def _subsetOf_[A](subset: _Set_[A], superset: _Set_[A]): Boolean = (subset, superset) match {
    case (_SNil_(), _) => true
    case (_, _SNil_()) => false
    case (_SCons_(h1, t1), _SCons_(h2, t2)) =>
      val c = _compare_(h1, h2)
      if (c < 0) false
      else if (c > 0) _subsetOf_(subset, t2)
      else _subsetOf_(t1, t2)
  }
  @library
  def _setIntersection_[A](s1: _Set_[A], s2: _Set_[A]): _Set_[A] = (s1, s2) match {
    case (_SNil_(), _) => s2
    case (_, _SNil_()) => s1
    case (_SCons_(h1, t1), _SCons_(h2, t2)) =>
      val c = _compare_(h1, h2)
      if (c < 0) _setIntersection_(t1, s2)
      else if (c > 0) _setIntersection_(s1, t2)
      else h1 :: _setIntersection_(t1, t2)
  }
  @library
  def _setUnion_[A](s1: _Set_[A], s2: _Set_[A]): _Set_[A] = (s1, s2) match {
    case (_SNil_(), _) => s2
    case (_, _SNil_()) => s1
    case (_SCons_(h1, t1), _SCons_(h2, t2)) =>
      val c = _compare_(h1, h2)
      if (c < 0) h1 :: _setUnion_(t1, s2)
      else if (c > 0) h2 :: _setUnion_(s1, t2)
      else h1 :: _setUnion_(t1, t2)
  }
  @library
  def _setDifference_[A](s1: _Set_[A], s2: _Set_[A]): _Set_[A] = (s1, s2) match {
    case (_SNil_(), _) => _SNil_()
    case (_, _SNil_()) => s1
    case (_SCons_(h1, t1), _SCons_(h2, t2)) =>
      val c = _compare_(h1, h2)
      if (c < 0) h1 :: _setDifference_(t1, s2)
      else if (c > 0) _setDifference_(s1, t2)
      else _setDifference_(t1, t2)
  }
 
  // We define our own lists to not have to load the entire scala lib
  @library
  sealed abstract class _Bag_[A]
  @library
  case class _BCons_[A](elem: A, mult: BigInt, t: _Bag_[A]) extends _Bag_[A]
  @library
  case class _BNil_[A]() extends _Bag_[A]

  @library
  def __BNil_$0ToString_[A](s: _Bag_[A]) = "Bag()"
  def __BCons_$0ToString_[A](s: _Bag_[A]) = {
    def rec(s: _Bag_[A]): String = s match {
      case _BCons_(e1, m1, b1@ _BCons_(_, _, _)) => _toString_(e1) + " -> " + _toString_(m1) + ", " + rec(b1)
      case _BCons_(e1, m1, _BNil_()) => _toString_(e1) + " -> " + _toString_(m1)
    }
    "Bag(" + rec(s) + ")"
  }

  @library @inline def min(b1: BigInt, b2: BigInt): BigInt = if (b1 <= b2) b1 else b2
  @library @inline def max(b1: BigInt, b2: BigInt): BigInt = if (b1 >= b2) b1 else b2

  @library
  def _bagAdd_[A](bag: _Bag_[A], elem: A, mult: BigInt): _Bag_[A] = bag match {
    case _BNil_() => _BCons_ (elem, mult, _BNil_())
    case _BCons_(h, m, t) =>
      val c = _compare_(elem, h)
      if (c < 0) _BCons_(elem, mult, bag)
      else if (c > 0) _BCons_(h, m, _bagAdd_(t, elem, mult))
      else _BCons_(h, m + mult, t)
  }
  @library
  def _bagMultiplicity_[A](bag: _Bag_[A], elem: A): BigInt = bag match {
    case _BNil_() => 0
    case _BCons_(h, m, t) =>
      val c = _compare_(elem, h)
      if (c < 0) 0
      else if (c > 0) _bagMultiplicity_(t, elem)
      else m
  }
  @library
  def _bagIntersection_[A](b1: _Bag_[A], b2: _Bag_[A]): _Bag_[A] = (b1, b2) match {
    case (_BNil_(), _) => b2
    case (_, _BNil_()) => b1
    case (_BCons_(h1, m1, t1), _BCons_(h2, m2, t2)) =>
      val c = _compare_(h1, h2)
      if (c < 0) _bagIntersection_(t1, b2)
      else if (c > 0) _bagIntersection_(b1, t2)
      else _BCons_(h1, min(m1, m2), _bagIntersection_(t1, t2))
  }
  @library
  def _bagUnion_[A](b1: _Bag_[A], b2: _Bag_[A]): _Bag_[A] = (b1, b2) match {
    case (_BNil_(), _) => b2
    case (_, _BNil_()) => b1
    case (_BCons_(h1, m1, t1), _BCons_(h2, m2, t2)) =>
      val c = _compare_(h1, h2)
      if (c < 0) _BCons_(h1, m1, _bagUnion_(t1, b2))
      else if (c > 0) _BCons_(h2, m2, _bagUnion_(b1, t2))
      else _BCons_(h1, m1 + m2, _bagUnion_(t1, t2))
  }
  @library
  def _bagDifference_[A](b1: _Bag_[A], b2: _Bag_[A]): _Bag_[A] = (b1, b2) match {
    case (_BNil_(), _) => _BNil_()
    case (_, _BNil_()) => b1
    case (_BCons_(h1, m1, t1), _BCons_(h2, m2, t2)) =>
      val c = _compare_(h1, h2)
      if (c < 0) _BCons_(h1, m1, _bagDifference_(t1, b2))
      else if (c > 0) _bagDifference_(b1, t2)
      else _BCons_(h1, max(0, m1 - m2), _bagDifference_(t1, t2))
  }
 
  @library
  sealed abstract class _Map_[K, V] {
    @inline def ::(key: K, value: V): _Map_[K, V] = _MCons_(key, value, this)
  }
  @library
  case class _MCons_[K, V](key: K, value: V, t: _Map_[K, V]) extends _Map_[K, V]
  @library
  case class _MNil_[K, V](default: V) extends _Map_[K, V]

  @library
  def __MNil_$0ToString_[K, V](s: _Map_[K, V]) = {
    val _MNil_(default) = s
    "Map()"
  }
  @library 
  def __MCons_$0ToString_[K, V](s: _Map_[K, V]) = {
    def vToString(v: V) = {
      val s = _toString_(v)
      s.bigSubstring(BigInt(5), s.bigLength - 1)
    }
    def rec(s: _Map_[K, V]): String = s match {
      case _MCons_(k1, v1, m1@ _MCons_(_, _, _)) =>
        _toString_(k1) + " -> " + vToString(v1) + ", " + rec(m1)
      case _MCons_(k1, v1, _MNil_(default)) =>
        _toString_(k1) + " -> " + vToString(v1)
    }
    "Map(" + rec(s) + ")"
  }

  @library
  def _mapApply_[K, V](map: _Map_[K, V], key: K): V = map match {
    case _MNil_(default) => default
    case _MCons_(k, v, t) =>
      if (k == key) v
      else _mapApply_(t, key)
  }
  @library
  def _mapUpdated_[K, V](map: _Map_[K, V], key: K, value: V): _Map_[K, V] = {
    map match {
      case _MNil_(default) => _MCons_(key, value, map)
      case _MCons_(k, v, t) =>
        if (k == key) _MCons_(key, value, t)
        else _MCons_(k, v, _mapUpdated_(t, key, value))
    } 
  }

}
