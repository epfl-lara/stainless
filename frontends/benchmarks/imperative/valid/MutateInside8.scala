import stainless.lang._
import stainless.annotation._

object MutateInside8 {
  case class Mut[@mutable T](var t: T)
  case class Thing[@mutable T](var field: T)

  def change_thing[@mutable T](mut: Mut[Thing[T]], v: T) = {
    mut.t = Thing(freshCopy(v))
  }

  def main() = {
    val thing = Thing(123)
    change_thing(Mut(thing), 456)
    assert(thing.field == 123)
  }
}
