import stainless.lang._

object Main {
  def f(thiss: A, oldThiss: A) = thiss != oldThiss
  case class A(var s: BigInt) derives CanEqual {
    def g() = {
      s = s + 1
      assert(f(this, old(this)))
    } 
  }
}
