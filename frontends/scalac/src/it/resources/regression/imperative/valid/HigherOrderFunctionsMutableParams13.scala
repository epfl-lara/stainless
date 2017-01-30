object HigherOrderFunctionsMutableParams13 {

  case class A(var x: BigInt)

  case class B(closure: (A) => BigInt) {

    def execute(a: A): BigInt = {
      a.x = a.x + 1
      closure(a)
    }

  }

  def test(): BigInt = {
    val a = A(3)
    val b = B((capturedA: A) => capturedA.x)

    b.execute(a)
    b.execute(a)
    b.execute(a)
  } ensuring(_ == 6)

}

