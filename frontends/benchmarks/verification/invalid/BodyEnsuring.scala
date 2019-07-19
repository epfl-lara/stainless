import stainless.lang._

object BodyEnsuring {
  def f(): () => Boolean = {
    () => {
      false 
    }.holds
  }

  def g() = {
    assert(f()())
    assert(false)
  }
}
