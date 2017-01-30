import stainless.lang._

object OldThis1 {

  case class A(var x: Int) {
    def foo(y: Int): Unit = {
      x += y
    } ensuring(_ => x == old(this).x + y)
  }

}
