import stainless.annotation._

object MutateInside3 {
  case class Mut[@mutable T](var t: T)
  case class Thing(var field: Int)

  def resetThing(m: Mut[Thing]): Unit = {
    m.t = Thing(0)
    m.t.field = 100
  }

  def main(): Unit = {
    val thing = Thing(123)
    resetThing(Mut(thing))
    assert(thing.field == 123)
  }
}
