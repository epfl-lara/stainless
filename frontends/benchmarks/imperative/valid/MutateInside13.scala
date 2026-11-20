import stainless.lang._
import stainless.annotation._

object MutateInside13 {
  case class Mut[@mutable T](var t: T)
  case class Thing[@mutable T](var field: T)

  def change_thing[@mutable T](mut: Mut[Thing[T]], v: T) = {
    mut.t = Thing(freshCopy(v))
  }

  def main() = {
    val thing = Thing(123)

    {
      val mut = Mut(thing)
      change_thing(mut, 789)
      mut.t.field = 500
    }

    assert(thing.field == 123)
  }
}
