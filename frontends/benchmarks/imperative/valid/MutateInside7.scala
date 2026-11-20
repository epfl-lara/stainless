import stainless.annotation._

object MutateInside7 {
  case class Mut[@mutable T](var t: T)
  case class Thing(var field: Int)

  def main(): Unit = {
    val thing = Thing(123)

    {
      val m = Mut(thing)
      m.t.field = 100
      m.t = Thing(0)
    }

    assert(thing.field == 100)
  }
}
