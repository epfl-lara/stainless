import stainless.collection._
import stainless.lang._
import stainless.annotation._

object Candidate2 {
  def uniq(lst: List[Int]): List[Int] = {
    decreases(lst.size)
    lst match {
      case Nil() => Nil()
      case Cons(hd, tl) =>
        def drop(a: Int, lst_0: List[Int]): List[Int] = {
          decreases(lst_0)
          lst_0 match {
            case Nil() => Nil()
            case Cons(hd_0, tl_0) =>
              if (a == hd_0) drop(a, tl_0) else hd_0 :: drop(a, tl_0)
          }
        }

        def lem(a: Int, @induct lst: List[Int]): Unit = {
          ()
        } ensuring(drop(a, lst).size <= lst.size)

        lem(hd, tl)
        assert(drop(hd, tl).size <= tl.size)
        assert(drop(hd, tl).size < lst.size)
        hd :: uniq(drop(hd, tl))
    }
  }
}
