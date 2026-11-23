/* Copyright 2009-2025 EPFL, Lausanne */

package stainless.collection


import scala.reflect.ClassTag
import stainless.lang.{ghost => ghostExpr, *}
import stainless.annotation.*
import stainless.collection.{List, Cons, Nil}
import stainless.lang.StaticChecks.*

/** A mutable array, backed by a native `Array` at runtime, whose specification is a `List`.
  */
@library
@mutable
case class LArray[T](private val data: Array[T]) {

  /** The abstraction of this array: its elements, in order. */
  @ghost @pure
  def toList(): List[T] = LArrayUtils.arrayToList(data, 0)

  def size: BigInt = {
    BigInt(data.length)
  }.ensuring(res => res == toList().size && 0 <= res && res <= BigInt(Int.MaxValue) && res.toInt == data.length)

  def isize: Int = {
    data.length
  }.ensuring(res => res == size.toInt && BigInt(res) == size && 0 <= res)

  def apply(i: BigInt): T = {
    require(0 <= i && i < size)
    ghostExpr({
      LArrayUtils.lemmaConversionBackForth(i)
      LArrayUtils.lemmaToIntBigIntConversionBothDirections(i, data.length)
      LArrayUtils.lemmaArrayToListApply(data, 0, i.toInt)
    })
    data(i.toInt)
  }.ensuring(res => res == toList()(i))

  def apply(i: Int): T = {
    require(0 <= i && i < isize)
    ghostExpr(LArrayUtils.lemmaArrayToListApply(data, 0, i))
    data(i)
  }.ensuring(res => res == toList()(BigInt(i)))

  def update(i: BigInt, v: T): Unit = {
    require(0 <= i && i < size)
    ghostExpr({
      LArrayUtils.lemmaConversionBackForth(i)
      LArrayUtils.lemmaToIntBigIntConversionBothDirections(i, data.length)
      LArrayUtils.lemmaArrayToListUpdated(data, 0, i.toInt, v)
    })
    data(i.toInt) = v
  }.ensuring(_ => toList() == old(this).toList().updated(i, v))

  def update(i: Int, v: T): Unit = {
    require(0 <= i && i < isize)
    ghostExpr(LArrayUtils.lemmaArrayToListUpdated(data, 0, i, v))
    data(i) = v
  }.ensuring(_ => toList() == old(this).toList().updated(BigInt(i), v))
}

@library
object LArray {
  def apply[T: ClassTag](size: BigInt, default: T): LArray[T] = {
    require(0 <= size && size <= BigInt(Int.MaxValue))
    ghostExpr(LArrayUtils.lemmaConversionBackForth(size))
    apply(size.toInt, default)
  }.ensuring(res => res.size == size && res.toList() == List.fill(size)(default))

  def apply[T: ClassTag](size: Int, default: T): LArray[T] = {
    require(0 <= size)
    val res = LArray(Array.fill[T](size)(default))
    ghostExpr({
      // before the fill lemma: its facts on `List.fill` make this simple conversion time out
      assert(res.size == BigInt(size))
      LArrayUtils.lemmaArrayToListFill(size, default, 0)
    })
    res
  }.ensuring(res => res.isize == size && res.size == BigInt(size) && res.toList() == List.fill(BigInt(size))(default))
}

@library
object LArrayUtils {

  /** The elements of `arr` from index `from` (included) to its end, in order.
    *
    * It is opaque, so that the VCs of the clients of `LArray` do not unroll it; the lemmas below unfold it.
    */
  @ghost @pure @opaque
  def arrayToList[T](arr: Array[T], from: Int): List[T] = {
    require(0 <= from && from <= arr.length)
    decreases(arr.length - from)
    if (from == arr.length) Nil[T]()
    else {
      additionIntPreservedByToBigInt(from, 1)
      Cons(arr(from), arrayToList(arr, from + 1))
    }
  }.ensuring(res => res.size == BigInt(arr.length) - BigInt(from))

  @ghost @opaque @inlineOnce
  def lemmaArrayToListApply[T](arr: Array[T], from: Int, i: Int): Unit = {
    require(0 <= from && from <= i && i < arr.length)
    decreases(i - from)
    unfold(arrayToList(arr, from))
    compareIntPreservedByToBigInt(from, i)
    compareIntPreservedByToBigInt(i, arr.length)
    additionIntPreservedByToBigInt(from, 1)
    if (from < i) lemmaArrayToListApply(arr, from + 1, i)
  }.ensuring(_ => arrayToList(arr, from)(BigInt(i) - BigInt(from)) == arr(i))

  /** Updating the array before `from` does not change its elements from `from` on. */
  @ghost @opaque @inlineOnce
  def lemmaArrayToListUpdatedBefore[T](arr: Array[T], from: Int, i: Int, v: T): Unit = {
    require(0 <= i && i < from && from <= arr.length)
    decreases(arr.length - from)
    unfold(arrayToList(arr, from))
    unfold(arrayToList(arr.updated(i, v), from))
    if (from < arr.length) {
      additionIntPreservedByToBigInt(from, 1)
      lemmaArrayToListUpdatedBefore(arr, from + 1, i, v)
    }
  }.ensuring(_ => arrayToList(arr.updated(i, v), from) == arrayToList(arr, from))

  @ghost @opaque @inlineOnce
  def lemmaArrayToListUpdated[T](arr: Array[T], from: Int, i: Int, v: T): Unit = {
    require(0 <= from && from <= i && i < arr.length)
    decreases(i - from)
    unfold(arrayToList(arr, from))
    unfold(arrayToList(arr.updated(i, v), from))
    compareIntPreservedByToBigInt(from, i)
    compareIntPreservedByToBigInt(i, arr.length)
    additionIntPreservedByToBigInt(from, 1)
    if (from < i) lemmaArrayToListUpdated(arr, from + 1, i, v)
    else lemmaArrayToListUpdatedBefore(arr, from + 1, i, v)
  }.ensuring(_ => arrayToList(arr.updated(i, v), from) == arrayToList(arr, from).updated(BigInt(i) - BigInt(from), v))

  @ghost @opaque @inlineOnce
  def lemmaArrayToListFill[T: ClassTag](n: Int, d: T, from: Int): Unit = {
    require(0 <= from && from <= n)
    decreases(n - from)
    unfold(arrayToList(Array.fill[T](n)(d), from))
    compareIntPreservedByToBigInt(from, n)
    if (from < n) {
      additionIntPreservedByToBigInt(from, 1)
      lemmaArrayToListFill(n, d, from + 1)
    }
  }.ensuring(_ => arrayToList(Array.fill[T](n)(d), from) == List.fill(BigInt(n) - BigInt(from))(d))

  @opaque @inlineOnce @ghost
  def compareIntPreservedByToBigInt(a: Int, b: Int): Unit = {
  }.ensuring(_ => (a < b) == (BigInt(a) < BigInt(b)) && (a > b) == (BigInt(a) > BigInt(b)) && (a == b) == (BigInt(a) == BigInt(b)))

  @opaque @inlineOnce @ghost
  def additionIntPreservedByToBigInt(a: Int, b: Int): Unit = {
    require(BigInt(a) + BigInt(b) <= BigInt(Int.MaxValue) && BigInt(a) + BigInt(b) >= BigInt(Int.MinValue))
  }.ensuring(_ => BigInt(a + b) == BigInt(a) + BigInt(b))

  @opaque @inlineOnce @ghost
  def lemmaToIntBigIntConversionBothDirections(a: BigInt, b: Int): Unit = {
    require(Int.MinValue <= a && a <= Int.MaxValue)
  }.ensuring(_ => (a.toInt == b) == (a == BigInt(b)) && (a < BigInt(b)) == (a.toInt < b) && (a > BigInt(b)) == (a.toInt > b) && (a <= BigInt(b)) == (a.toInt <= b) && (a >= BigInt(b)) == (a.toInt >= b))

  @opaque @inlineOnce @ghost
  def lemmaConversionBackForth(a: BigInt): Unit = {
    require(Int.MinValue <= a && a <= Int.MaxValue)
  }.ensuring(_ => a == BigInt(a.toInt))
}
