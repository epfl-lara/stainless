import stainless.lang.{ghost => ghostExpr, *}
import stainless.annotation.*
import stainless.collection.*
import stainless.lang.StaticChecks.*

/** `LArray` is a mutable array, backed by a native `Array` at runtime, whose specification is a ghost `List`.
  *
  * This example follows the pattern used by Ziplex (in Bolts) with its `Sequence`: the specification is written and
  * reasoned about with purely functional functions on `List`, while the executable code is imperative and index-based
  * on the efficient data structure, and is proven equivalent to the specification through `getList`.
  */
object LArrayExample01 {

  // ---------------------------------------------- Specification, on List ---------------------------------------------

  def sumList(l: List[BigInt]): BigInt = {
    decreases(l)
    l match {
      case Nil() => BigInt(0)
      case Cons(h, t) => h + sumList(t)
    }
  }

  // --------------------------------------- Lemmas, on List only (no array involved) ----------------------------------

  @ghost @opaque @inlineOnce
  def lemmaDropApply[T](l: List[T], i: BigInt): Unit = {
    require(0 <= i && i < l.size)
    decreases(l)
    l match {
      case Cons(_, t) if i > 0 => lemmaDropApply(t, i - 1)
      case _ => ()
    }
  }.ensuring(_ => l.drop(i) == Cons(l(i), l.drop(i + 1)))

  @ghost @opaque @inlineOnce
  def lemmaDropSizeIsNil[T](l: List[T]): Unit = {
    decreases(l)
    l match {
      case Cons(_, t) => lemmaDropSizeIsNil(t)
      case Nil() => ()
    }
  }.ensuring(_ => l.drop(l.size) == Nil[T]())

  @ghost @opaque @inlineOnce
  def lemmaSumListUpdated(l: List[BigInt], i: BigInt, v: BigInt): Unit = {
    require(0 <= i && i < l.size)
    decreases(l)
    l match {
      case Cons(_, t) if i > 0 => lemmaSumListUpdated(t, i - 1, v)
      case _ => ()
    }
  }.ensuring(_ => sumList(l.updated(i, v)) == sumList(l) - l(i) + v)

  // ------------------------------------------ Implementation, on LArray ----------------------------------------------

  /** Sums the elements with a loop and constant-time accesses; the result is the one of the `List` specification. */
  def sum(a: LArray[BigInt]): BigInt = {
    require(a.valid)
    var i = BigInt(0)
    var acc = BigInt(0)
    (while (i < a.size) {
      decreases(a.size - i)
      ghostExpr(lemmaDropApply(a.getList, i))
      acc = acc + a(i)
      i = i + 1
    }).invariant(a.valid && 0 <= i && i <= a.size && acc + sumList(a.getList.drop(i)) == sumList(a.getList))
    ghostExpr(lemmaDropSizeIsNil(a.getList))
    acc
  }.ensuring(res => res == sumList(a.getList))

  /** In-place update of one cell; its effect is specified on the `List` view of the array. */
  def addAt(a: LArray[BigInt], i: BigInt, d: BigInt): Unit = {
    require(a.valid)
    require(0 <= i && i < a.size)
    a(i) = a(i) + d
  }.ensuring(_ => a.valid && a.getList == old(a).getList.updated(i, old(a).getList(i) + d))

  /** A client mutating the array: the reasoning about the mutation is done entirely with a lemma on `List`. */
  def addAtThenSum(a: LArray[BigInt], i: BigInt, d: BigInt): BigInt = {
    require(a.valid)
    require(0 <= i && i < a.size)
    @ghost val before = a.getList
    addAt(a, i, d)
    ghostExpr(lemmaSumListUpdated(before, i, before(i) + d))
    sum(a)
  }.ensuring(res => a.valid && res == sumList(old(a).getList) + d)
}
