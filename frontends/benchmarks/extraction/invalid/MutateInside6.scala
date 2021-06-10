import stainless.annotation._

object MutateInside6 {
  case class Mut[@mutable T](var t: T)
  case class Thing(var field: Int)

  def resetThing(m: Mut[Thing]): Unit = {
    m.t.field = 100
    m.t = Thing(0)
  }

  def main(): Unit = {
    val thing = Thing(123)

    {
      val m = Mut(thing)
      resetThing(m)
    }

    assert(thing.field == 100)
  }
}
