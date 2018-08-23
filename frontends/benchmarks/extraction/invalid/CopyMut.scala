import stainless.lang._

object CopyMut {

  case class Toto(var x: Int)

  case class Foo(bar: Int, var toto: Toto) {
    def double: Foo = this.copy(bar = bar * 2)
  }

  def prop = (Foo(41, Toto(1)).double.bar == 84).holds

}
