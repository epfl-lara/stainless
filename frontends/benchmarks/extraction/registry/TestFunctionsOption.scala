
import stainless.lang._

// Use with --functions=theorem
// Expect invalid result.
object TestFunctionsOption {

  def skipped1: Boolean = { true }.holds
  def skipped2: Boolean = { false }.holds

  def theorem(foo: Foo): Boolean = {
    foo.method == 42
  }.holds

  /* NON SEALED */ abstract class Foo { def method: BigInt }
  case class Bar() extends Foo { override def method: BigInt = 0 }

}

