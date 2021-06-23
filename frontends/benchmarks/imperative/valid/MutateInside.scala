import stainless.annotation._

object MutateInside {
  case class Thing(var field: Int)

  def resetThing(t: Thing): Unit = {
    t.field = 0
  }

  def main(): Unit = {
    var x = 100
    resetThing(Thing(x))
    assert(x == 100)
  }
}
