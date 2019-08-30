import stainless.lang._

object OldThis4 {

  case class A(var a: Int) {
    def foo(b: Int): Unit = {
      b + b // a never used
      ()
    } ensuring(_ => a == old(this).a)
  }

}
