object TypeMember {
  abstract class M {
    type T
    def c(t: T): Unit
  }

  case class A(var x: BigInt)

  case class F() extends M {
    type T = A
    def c(t: T) = {
      t.x += 2
    }
  }
}
