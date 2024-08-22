import stainless.annotation._
import stainless.lang._
import stainless.io._

object FindIndex {
  def containsFrom[T](a: Array[T], t: T, j: Int): Boolean = {
    require(0 <= j && j < a.length)
    var i = j
    (while (i < a.length) {
      decreases(a.length - i)
      if (a(i) == t) return true
      i += 1
    }).invariant(j <= i)
    false
  }

  @pure @extern // admitted lemma
  def containsFromLemma[T](a: Array[T], t: T, j: Int): Unit = {
    require(0 <= j && j < a.length && containsFrom(a, t, j) && a(j) != t)

 }.ensuring(_ =>
    containsFrom(a, t, j + 1)
  )

  @inline
  def contains[T](a: Array[T], t: T): Boolean = a.length > 0 && containsFrom(a, t, 0)

  def testContains: Unit = {
    assert(contains(Array(0,100,200,250), 0))
    assert(contains(Array(0,100,200,250), 100))
    assert(contains(Array(0,100,200,250), 200))
    assert(contains(Array(0,100,200,250), 250))
    assert(!contains(Array(0,100,200,250), 150))
  }

  def findIndex[T](a: Array[T], t: T): Int = {
    require(contains(a, t))

    var i: Int = 0
    (while (true) {
      decreases(a.length - i)
      if (a(i) == t) return i
      containsFromLemma(a, t, i)
      i += 1
    }).invariant(0 <= i && i < a.length && (
      a(i) == t ||
      containsFrom(a, t, i)
    ))
    assert(false)
    0
  }

  def testFindIndex: Unit = {
    assert(findIndex(Array(0,100,200,250), 0) == 0)
    assert(findIndex(Array(0,100,200,250), 100) == 1)
    assert(findIndex(Array(0,100,200,250), 200) == 2)
    assert(findIndex(Array(0,100,200,250), 250) == 3)
  }

  @extern
  def main(args: Array[String])(implicit @ghost state: State): Unit = {
    val a = Array(0, 100, 150, 300)
    StdOut.println(findIndex(a, 150))
  }
}
