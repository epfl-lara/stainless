// import stainless.lang._

object TraitVar1 {

  sealed trait Foo {
    var prop: BigInt

  }

  case class Bar(var prop: BigInt) extends Foo {


    // def doStuff(x: BigInt) = {
    //   prop = prop + x
    // }

  }

  def theorem(foo: Foo) = {
    val prev = foo.prop
    foo.prop = foo.prop + 1
    // foo.doStuff(2)
    foo.prop == prev + 2
  } // .holds

}
