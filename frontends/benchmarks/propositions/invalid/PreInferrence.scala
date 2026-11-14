import stainless.lang._

object PreInferrence {
  def isForall(b: Boolean): (Boolean => Boolean) => Boolean = {
    (p: Boolean => Boolean) => b == forall(p)
  }
}
