import stainless.lang._

object OldThis2 {

  case class B(var x: Int)

  case class A(b: B) {
    def foo(y: Int): Unit = {
      b.x += y
    } ensuring(_ => b.x == old(this).b.x + y)
  }

}
