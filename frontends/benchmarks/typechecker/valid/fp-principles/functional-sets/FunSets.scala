/* Copyright 2017- LARA, EPFL, Lausanne.
   Author: Dragana Milovancevic. */
package funsets

import stainless.lang._
import stainless.annotation._
import stainless.collection._

// Purely Functional Sets.
object FunSets {
  // We represent a set by its characteristic function, `contains`

  // Indicates whether a set contains a given element.
  def contains(s: Int => Boolean, elem: Int): Boolean = s(elem)

  // Complement of `s`
  def complement(s: Int => Boolean): Int => Boolean = (e: Int) => !s(e)

  // check that every element is in the set or its complement
  def checkComplement(e: Int, s: Int => Boolean) : Boolean =
    (contains(s, e) || contains(complement(s),e)).holds

  // The set containing the given element and nothing else
  def singletonSet(elem: Int): Int => Boolean = (e: Int) => elem == e

  // check that singleton does contain the element
  def checkContains(elem: Int) : Boolean =
    contains(singletonSet(elem), elem).holds

  // check that distinct elements give distinct singletons
  def checkSingleton(e1: Int, e2:Int, s: Int => Boolean): Boolean =
     (e1==e2 ||
      contains(singletonSet(e1), e1) && !(contains(singletonSet(e1), e2))).holds

  // Union of the two given sets, whose elements that in `s` or `t`
  def union(s: Int => Boolean, t: Int => Boolean): Int => Boolean =
    (elem: Int) => s(elem) || t(elem)

  // check if an element is in one of the sets, it is in the union
  def checkUnion1(s1: Int=>Boolean, s2: Int => Boolean, e: Int): Boolean =
     ((!contains(s1, e) && !contains(s2, e)) ||
      (contains(union(s1, s2), e))).holds

  // check if element is in union, it is in one of the sets
  def checkUnion2(s1: Int=>Boolean, s2: Int => Boolean, e: Int) : Boolean =
     ((!contains(union(s1, s2), e)) || (contains(s1, e) || contains(s2, e)) ).holds

  // Intersection of the two given sets: elements both in `s` and `t`
  def intersect(s: Int => Boolean, t: Int => Boolean): Int => Boolean =
     (elem: Int) => s(elem) && t(elem)

  // check if set is in intersection, it is in both sets
  def checkIntersect(s1: Int => Boolean, s2: Int => Boolean, e: Int): Boolean =
     ((contains(s1, e) && contains(s2, e)) || (!contains(intersect(s1, s2), e))).holds


  // Difference of the two given sets, elements of `s` that are not in `t`.
  def diff(s: Int => Boolean, t: Int => Boolean): Int => Boolean =
     (elem: Int) => s(elem) && !t(elem)

  // check if element is in the intersection it is in `s1` and not `s2`
  def checkDiff(s1: Int => Boolean, s2: Int => Boolean, e: Int): Boolean =
     (!contains(diff(s1, s2), e) || (contains(s1, e) && !contains(s2, e))).holds

  /**
   * Returns the subset of `s` for which `p` holds.
   */
  def filter(s: Int => Boolean, p: Int => Boolean): Int => Boolean = {
    (elem: Int) => s(elem) && p(elem)
  }
  // ensuring(res => forallCheck(res, p))

  def filterIterForallCheck(a: Int, s: Int => Boolean, p: Int => Boolean): Boolean = {
    decreases(if (a < 0) -(a + 1) else 0, max(0, bound - a + 1))
    val res = filter(s, p)

    if (a > bound) ()
    else if (res(a) && !p(a)) ()
    else filterIterForallCheck(a+1, s, p)

    iterForallCheck(a, res, p)
  }.holds

  def filterForallCheck(s: Int => Boolean, p: Int => Boolean): Boolean = {
    filterIterForallCheck(-bound, s, p)
    val res = filter(s, p)
    forallCheck(res, p)
  }.holds

  // The bounds on absolute value of `forallCheck` and `existsCheck`
  val bound = 1000

  def max(x: Int, y: Int) = if (x > y) x else y

  // Check for bounded range if all `s` satisfy `p`
  def iterForallCheck(a: Int, s: Int => Boolean, p: Int => Boolean): Boolean = {
    decreases(if (a < 0) -(a + 1) else 0, max(0, bound - a + 1))
    if (a > bound) true
    else if (s(a) && !p(a)) false
    else iterForallCheck(a+1, s, p)
  }

  def forallCheck(s: Int => Boolean, p: Int => Boolean): Boolean = {
    iterForallCheck(-bound, s, p)
  }

  // Check if exists an integer in the bound and within `s` that satisfies `p`
  def existsCheck(s: Int => Boolean, p: Int => Boolean): Boolean = {
    if(forallCheck(s, (elem:Int) => !p(elem))) false
    else true
  }

  // either set `s` its complement are nonempty
  def checkExists(s: Int=>Boolean) : Boolean =
    (existsCheck(s, _=>true) || existsCheck(complement(s),_=>true)).holds

  // Set computed by applying `f` to each element of `s`
  def iterMap(newset: Int => Boolean, a: Int, s: Int => Boolean, f: Int => Int): Int => Boolean = {
    decreases(if (a < 0) -(a + 1) else 0, max(0, bound - a + 1))
    if(a > bound) newset
    else if (s(a)) iterMap(union(newset, singletonSet(f(a))), a+1, s, f)
    else iterMap(newset, a+1, s, f)
  }

  def map(s: Int => Boolean, f: Int => Int): Int => Boolean = {
    iterMap(Int => false, -bound, s, f)
  }

  def checkSet1(s1: Int => Boolean, s2: Int => Boolean, x: Int): Boolean =
    (intersect(s1, s2)(x) == complement(union(complement(s1), complement(s2)))(x)).holds

  def checkSet2(s1: Int => Boolean, s2: Int => Boolean, x: Int): Boolean =
    (union(s1, s2)(x) == complement(intersect(complement(s1), complement(s2)))(x)).holds
}
