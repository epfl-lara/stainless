import stainless.lang._
import stainless.proof._
import stainless.annotation._

// A variant of ForestNothing2, that also works by creating an inexisting object out of a function.
object MakeFalse {

  // The dummy Int is there to ensure that the Scala compiler does not synthesize
  // a default-constructed False object (which would trigger the class invariant).
  case class False(dummy: Int) {
    require(false)
  }

  def chooseFn[A, B]: A => B = choose[A => B](f => true)

  def mkFalse: False = {
    // choose((x: False) => true) rejected due to quantification not fitting
    // in supported fragment (due to ADT invariant)
    val fn = chooseFn[BigInt, False]
    fn(42)
  }

  def theorem: Unit = {
    val f: False = mkFalse
    // Trying to trick the solver to unfold the class invariant by gesticulating
    assert(f == f)
    val x = f.dummy
    assert(f.dummy == x)
    assert(false)
    ()
  }
}
