import stainless.lang._

object OldThis3 {

  case class A(var a: Int) {
    def foo(b: Int): Unit = {
      a + b // no assignement
      ()
    } ensuring(_ => a == old(this).a)
  }

}
