import stainless.lang._

object TraitVar1 {

  sealed trait Foo {
    var prop: BigInt

    def getProp: BigInt
    def setProp(x: BigInt): Unit

    def doStuff(x: BigInt) = {
      setProp(x)
    }
  }

  case class Bar(var prop: BigInt) extends Foo {
    def getProp: BigInt = prop + 1
    def setProp(y: BigInt): Unit = prop = y * 2
  }

  def theorem(foo: Foo) = {
    require(foo.isInstanceOf[Bar])
    foo.doStuff(2)
    foo.getProp == 5
  }.holds

}
