import stainless.lang._
import stainless.annotation._

object SimpleImperative {
  @mutable abstract class A {
    def f(): Unit 
  }

  def proc(a: A) = {
    a.f()
  }

  case class B(var x: BigInt) extends A {
    def f(): Unit = {
      x = x + 1
    }
  }

  def theorem() = {
    val a = B(0)
    proc(a)
    assert(a.x == 0) // should be 1
  }
}
