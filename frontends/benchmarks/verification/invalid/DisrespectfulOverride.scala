object DisrespectfulOverride {
  abstract class A {
    def f(): BigInt = {
      ??? : BigInt
    }.ensuring(_ > 0)
  }

  case class C() extends A {
    override def f() = 0
  }
}
