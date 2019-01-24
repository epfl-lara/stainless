package stainless.wasm

import stainless.lang._
import stainless.annotation.library

/** Implements tuples,
  * as well as set, map and bag operations on top of sorted lists
  */
@library
object Runtime {

  @library
  sealed case class Tuple2[T1, T2](e1: T1, e2: T2)
  @library
  sealed case class Tuple3[T1, T2, T3](e1: T1, e2: T2, e3: T3)
  @library
  sealed case class Tuple4[T1, T2, T3, T4](e1: T1, e2: T2, e3: T3, e4: T4)

  /* Transforms any type to a string.  Will be filled in by the code generator */
  @library
  def toString[A](a: A): String = ""

  /* String transformers for basic types */
	@library
  def digitToStringL(b: Long): String = {
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
  def digitToStringI(b: Int): String = {
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
  def i64ToString(b: Long): String = {
    if (b < 0) "-" + i64ToString(-b)
    else if (b <= 9) digitToStringL(b)
    else i64ToString(b / 10) + digitToStringL(b % 10)
  }

	@library
  def i32ToString(b: Int): String = {
    if (b < 0) "-" + i32ToString(-b)
    else if (b <= 9) digitToStringI(b)
    else i32ToString(b / 10) + digitToStringI(b % 10)
  }


	@library
	def booleanToString(i: Int) = if (i == 0) "false" else "true"
	@library // TODO
	def f64ToString(b: Real): String = "<real>"
	@library
	def funToString(): String = "<function>"
	@library
	def unitToString(): String = "()"

  /* compares two elements of any type. Will be filled in by the code generator */
  @library
  def compare[A](a1: A, a2: A): Int = 0

  // We define our own lists to not have to load the entire scala lib
  @library
  sealed abstract class Set[A] {
    @inline def ::(elem: A): Set[A] = SCons(elem, this)
  }
  @library
  case class SCons[A](h: A, t: Set[A]) extends Set[A]
  @library
  case class SNil[A]() extends Set[A]

  @library
  def SNil$0ToString[A](s: Set[A]) = "Set()"
  @library
  def SCons$0ToString[A](s: Set[A]) = {
    def rec(s: Set[A]): String = s match {
      case SCons(e1, s1@ SCons(_, _)) => toString[A](e1) + ", " + rec(s1)
      case SCons(e1, SNil()) => toString[A](e1)
    }
    "Set(" + rec(s) + ")"
  }

  @library
  def setAdd[A](set: Set[A], elem: A): Set[A] = set match {
    case SNil() => elem :: SNil()
    case SCons(h, t) =>
      val c = compare(elem, h)
      if (c < 0) elem :: h :: t
      else if (c > 0) h :: setAdd(t, elem)
      else h :: t
  }
  @library
  def elementOfSet[A](set: Set[A], elem: A): Boolean = set match {
    case SNil() => false
    case SCons(h, t) =>
      val c = compare(elem, h)
      if (c < 0) false
      else if (c > 0) elementOfSet(t, elem)
      else true
  }
  @library
  def subsetOf[A](subset: Set[A], superset: Set[A]): Boolean = (subset, superset) match {
    case (SNil(), _) => true
    case (_, SNil()) => false
    case (SCons(h1, t1), SCons(h2, t2)) =>
      val c = compare(h1, h2)
      if (c < 0) false
      else if (c > 0) subsetOf(subset, t2)
      else subsetOf(t1, t2)
  }
  @library
  def setIntersection[A](s1: Set[A], s2: Set[A]): Set[A] = (s1, s2) match {
    case (SNil(), _) => s2
    case (_, SNil()) => s1
    case (SCons(h1, t1), SCons(h2, t2)) =>
      val c = compare(h1, h2)
      if (c < 0) setIntersection(t1, s2)
      else if (c > 0) setIntersection(s1, t2)
      else h1 :: setIntersection(t1, t2)
  }
  @library
  def setUnion[A](s1: Set[A], s2: Set[A]): Set[A] = (s1, s2) match {
    case (SNil(), _) => s2
    case (_, SNil()) => s1
    case (SCons(h1, t1), SCons(h2, t2)) =>
      val c = compare(h1, h2)
      if (c < 0) h1 :: setUnion(t1, s2)
      else if (c > 0) h2 :: setUnion(s1, t2)
      else h1 :: setUnion(t1, t2)
  }
  @library
  def setDifference[A](s1: Set[A], s2: Set[A]): Set[A] = (s1, s2) match {
    case (SNil(), _) => SNil()
    case (_, SNil()) => s1
    case (SCons(h1, t1), SCons(h2, t2)) =>
      val c = compare(h1, h2)
      if (c < 0) h1 :: setDifference(t1, s2)
      else if (c > 0) setDifference(s1, t2)
      else setDifference(t1, t2)
  }

  // We define our own lists to not have to load the entire scala lib
  @library
  sealed abstract class Bag[A]
  @library
  case class BCons[A](elem: A, mult: BigInt, t: Bag[A]) extends Bag[A]
  @library
  case class BNil[A]() extends Bag[A]

  @library
  def BNil$0ToString[A](s: Bag[A]) = "Bag()"
  @library
  def BCons$0ToString[A](s: Bag[A]) = {
    def rec(s: Bag[A]): String = s match {
      case BCons(e1, m1, b1@ BCons(_, _, _)) => toString(e1) + " -> " + toString(m1) + ", " + rec(b1)
      case BCons(e1, m1, BNil()) => toString(e1) + " -> " + toString(m1)
    }
    "Bag(" + rec(s) + ")"
  }

  @library @inline def min(b1: BigInt, b2: BigInt): BigInt = if (b1 <= b2) b1 else b2
  @library @inline def max(b1: BigInt, b2: BigInt): BigInt = if (b1 >= b2) b1 else b2

  @library
  def bagAdd[A](bag: Bag[A], elem: A, mult: BigInt): Bag[A] = bag match {
    case BNil() => BCons (elem, mult, BNil())
    case BCons(h, m, t) =>
      val c = compare(elem, h)
      if (c < 0) BCons(elem, mult, bag)
      else if (c > 0) BCons(h, m, bagAdd(t, elem, mult))
      else BCons(h, m + mult, t)
  }
  @library
  def bagMultiplicity[A](bag: Bag[A], elem: A): BigInt = bag match {
    case BNil() => 0
    case BCons(h, m, t) =>
      val c = compare(elem, h)
      if (c < 0) 0
      else if (c > 0) bagMultiplicity(t, elem)
      else m
  }
  @library
  def bagIntersection[A](b1: Bag[A], b2: Bag[A]): Bag[A] = (b1, b2) match {
    case (BNil(), _) => b2
    case (_, BNil()) => b1
    case (BCons(h1, m1, t1), BCons(h2, m2, t2)) =>
      val c = compare(h1, h2)
      if (c < 0) bagIntersection(t1, b2)
      else if (c > 0) bagIntersection(b1, t2)
      else BCons(h1, min(m1, m2), bagIntersection(t1, t2))
  }
  @library
  def bagUnion[A](b1: Bag[A], b2: Bag[A]): Bag[A] = (b1, b2) match {
    case (BNil(), _) => b2
    case (_, BNil()) => b1
    case (BCons(h1, m1, t1), BCons(h2, m2, t2)) =>
      val c = compare(h1, h2)
      if (c < 0) BCons(h1, m1, bagUnion(t1, b2))
      else if (c > 0) BCons(h2, m2, bagUnion(b1, t2))
      else BCons(h1, m1 + m2, bagUnion(t1, t2))
  }
  @library
  def bagDifference[A](b1: Bag[A], b2: Bag[A]): Bag[A] = (b1, b2) match {
    case (BNil(), _) => BNil()
    case (_, BNil()) => b1
    case (BCons(h1, m1, t1), BCons(h2, m2, t2)) =>
      val c = compare(h1, h2)
      if (c < 0) BCons(h1, m1, bagDifference(t1, b2))
      else if (c > 0) bagDifference(b1, t2)
      else BCons(h1, max(0, m1 - m2), bagDifference(t1, t2))
  }

  @library
  sealed abstract class Map[K, V] {
    @inline def ::(key: K, value: V): Map[K, V] = MCons(key, value, this)
  }
  @library
  case class MCons[K, V](key: K, value: V, t: Map[K, V]) extends Map[K, V]
  @library
  case class MNil[K, V](default: V) extends Map[K, V]

  @library
  def MNil$0ToString[K, V](s: Map[K, V]) = {
    "Map()"
  }
  @library
  def MCons$0ToString[K, V](s: Map[K, V]) = {
    def vToString(v: V) = {
      val s = toString(v)
      s.bigSubstring(BigInt(5), s.bigLength - 1)
    }
    def rec(s: Map[K, V]): String = s match {
      case MCons(k1, v1, m1@ MCons(_, _, _)) =>
        toString(k1) + " -> " + vToString(v1) + ", " + rec(m1)
      case MCons(k1, v1, MNil(default)) =>
        toString(k1) + " -> " + vToString(v1)
    }
    "Map(" + rec(s) + ")"
  }

  @library
  def mapApply[K, V](map: Map[K, V], key: K): V = map match {
    case MNil(default) => default
    case MCons(k, v, t) =>
      if (k == key) v
      else mapApply(t, key)
  }
  @library
  def mapUpdated[K, V](map: Map[K, V], key: K, value: V): Map[K, V] = {
    map match {
      case MNil(default) => MCons(key, value, map)
      case MCons(k, v, t) =>
        if (k == key) MCons(key, value, t)
        else MCons(k, v, mapUpdated(t, key, value))
    }
  }

}
