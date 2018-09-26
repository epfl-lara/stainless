import stainless.lang._

object TraitVar2 {

  sealed trait Foo {
    var prop: BigInt

    def doStuff(x: BigInt) = {
      prop = x
    }
  }

  case class Bar(var stuff: BigInt) extends Foo {
    def prop: BigInt = stuff + 1
    def prop_=(y: BigInt): Unit = {
      stuff = y * 2
    }
  }

  def theorem(foo: Foo) = {
    require(foo.isInstanceOf[Bar])
    foo.doStuff(2)
    foo.prop == 5
  }.holds

}
