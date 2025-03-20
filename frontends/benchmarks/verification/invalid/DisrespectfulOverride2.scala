object DisrespectfulOverride2 {
  abstract class A {
    def f(): BigInt = {
      ??? : BigInt
    }.ensuring(_ > 0)
  }

  abstract class B extends A

  case class C() extends B {
    override def f() = 0
  }
}
