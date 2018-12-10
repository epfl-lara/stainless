import stainless.annotation._

object RefinedInnerImperative {

  @mutable
  trait A

  case class Counter(var x: BigInt) {
    def reset() = x = 0
  }

  case class B(val c: Counter) extends A {
    def f() = {
      while(true) {
        c.reset()
      }
    }
  }

}
