import stainless.lang._

object Copy {

  case class Foo(bar: Int, var toto: Boolean) {
    def double: Foo = this.copy(bar = bar * 2)
  }

  def prop = (Foo(41, true).double.bar == 82).holds

}
