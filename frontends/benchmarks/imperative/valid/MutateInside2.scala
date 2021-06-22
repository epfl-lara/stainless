import stainless.annotation._

object MutateInside2 {
  case class Mut[@mutable T](var t: T)
  case class Thing(var field: Int)

  def resetThing(m: Mut[Thing]): Unit = {
    m.t = Thing(0)
  }

  def main(): Unit = {
    val thing = Thing(123)
    resetThing(Mut(thing))
    assert(thing.field == 123)
  }
}
