import stainless.lang._

object i1214a {
  abstract sealed class Ordinal {
    def l: BigInt = {
      this match {
        case Nat() => BigInt(0)
        case Transfinite(in) => in.l + 1
      }
    }.ensuring(res => res >= 0)
  }

  case class Nat() extends Ordinal
  case class Transfinite(in: Ordinal) extends Ordinal //removing Ordinal removes location information

  object lemmas {
    def bar(a: Ordinal): Unit = {
      decreases(a.l, 1)
      def helper(c: Transfinite): Unit = {
        decreases(c.l, 0)
        assert(c.isInstanceOf[Transfinite])
        bar(c.in)
      }

      a match {
        case b: Transfinite =>
          helper(b)
        case Nat() =>
      }
    }
  }
}