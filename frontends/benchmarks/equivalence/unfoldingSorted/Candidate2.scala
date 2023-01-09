import stainless.lang._
import stainless.collection._

object Candidate2 {

  def unfoldingSorted[State, Elem](start: State,
                                   next: State => Option[(Elem, State)], // oops, should be State, Elem not Elem, State
                                   leq: (Elem, Elem) => Boolean,
                                   max: BigInt): List[Elem] = {
    def insertSorted(t: Elem, xs: List[Elem]): List[Elem] = {
      decreases(xs)
      xs match {
        case Nil() => Cons(t, Nil())
        case Cons(hd, tl) =>
          if (leq(t, hd)) t :: xs
          else Cons(hd, insertSorted(t, tl))
      }
    }
    def go(s: State, xs: List[Elem], fuel: BigInt): List[Elem] = {
      decreases(if (fuel <= 0) BigInt(0) else fuel)
      if (fuel <= 0) xs
      else next(s) match {
        case Some((t, nxtS)) =>
          go(nxtS, insertSorted(t, xs), fuel - 1)
        case None() => xs
      }
    }

    go(start, Nil(), max)
  }
}