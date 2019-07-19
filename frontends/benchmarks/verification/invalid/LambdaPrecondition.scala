import stainless.lang._

object LambdaPreconditions {
  def a() = {
    require(false)
    false
  }.holds

  def f(b: Boolean): () => Boolean = {
    if (b) a
    else () => true
  }

  def g() = {
    assert(f(true)())
    assert(false)
  }
}
