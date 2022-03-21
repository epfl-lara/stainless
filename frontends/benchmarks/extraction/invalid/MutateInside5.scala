import stainless.annotation._

// FIXME: Used to be accepted and verified (now rejected at extraction)
object MutateInside5 {
  case class Mut[@mutable T](var t: T)
  case class Thing(var field: Int)

  def resetThing(m: Mut[Thing]): Unit = {
    m.t = Thing(0)
  }

  def main(): Unit = {
    val thing = Thing(123)

    {
      // "Unsupported val definition (couldn't compute targets and there are mutable variables shared between the binding and the body)"
      // This test case used to be accepted because a special case was triggered in AntiAliasing due to `thing` not being referenced
      // in the body of the block.
      // Now, the Normalizer removes the inner block and that special case is no longer triggered
      // (because `thing` is now referenced by the assertion below)
      val m = Mut(thing)
      resetThing(m)
    }

    assert(thing.field == 123)
  }
}
