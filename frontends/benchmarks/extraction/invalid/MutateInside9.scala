import stainless.lang._
import stainless.annotation._

// FIXME: Used to be accepted and verified (now rejected at extraction)
object MutateInside9 {
  case class Mut[@mutable T](var t: T)
  case class Thing[@mutable T](var field: T)

  def change_thing[@mutable T](mut: Mut[Thing[T]], v: T) = {
    mut.t = Thing(freshCopy(v))
  }

  def main() = {
    val thing = Thing(123)

    {
      // "Unsupported val definition (couldn't compute targets and there are mutable variables shared between the binding and the body)"
      // This test case used to be accepted because a special case was triggered in AntiAliasing due to `thing` not being referenced
      // in the body of the block.
      // Now, the Normalizer removes the inner block and that special case is no longer triggered
      // (because `thing` is now referenced by the assertion below)
      val mut = Mut(thing)
      change_thing(mut, 789)
    }

    assert(thing.field == 123)
  }
}
