import stainless.lang._
import stainless.annotation._

object MutateInside10 {
  case class Mut[@mutable T](var t: T)
  case class Thing[@mutable T](var field: T)

  def change_thing[@mutable T](mut: Mut[Thing[T]], v: T) = {
    mut.t = Thing(freshCopy(v))
  }

  def main() = {
    val thing = Thing(123)

    {
      val mut = Mut(thing)
      mut.t.field = 222
    }

    assert(thing.field == 222)

  }
}
