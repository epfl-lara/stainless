import stainless.lang._
import stainless.io._
import stainless.annotation._

object Return {

  def return10: Int = {
    return 10
  }

  def findIndex[T](a: Array[T], t: T): Int = {
    var i: Int = 0
    (while (i < a.length) {
      decreases(a.length - i)
      if (a(i) == t) return i
      i += 1
    }).invariant(0 <= i && i <= a.length)

    0
  }

  def verify(b: Boolean)(implicit @ghost state: State) = {
    require(b)
    if (b) StdOut.println("OK")
    else StdOut.println("ERROR")
  }

  @cCode.`export`
  def main() = {
    @ghost implicit val state = newState
    verify(return10 == 10)
    verify(findIndex(Array(0,100,200,250), 0) == 0)
    verify(findIndex(Array(0,100,200,250), 100) == 1)
    verify(findIndex(Array(0,100,200,250), 200) == 2)
    verify(findIndex(Array(0,100,200,250), 250) == 3)
  }

}
