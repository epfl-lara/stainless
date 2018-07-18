import stainless.lang._

object DefaultParam {

  case class Foo(bar: Int, var toto: Boolean) {
    def plus(x: Int = 1): Foo = Foo(bar + x, true)
  }

  def abc = (Foo(41, true).plus().bar == 42).holds

}
