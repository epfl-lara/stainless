import stainless.annotation._

trait HiddenOverride {
  def f() = 0

  def g() = {
    val x = f() 
    // f may have been overridden, so the assert doesn't always hold
    assert(x == 0)
  }
}
