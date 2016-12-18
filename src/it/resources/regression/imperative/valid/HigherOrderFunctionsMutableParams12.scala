object HigherOrderFunctionsMutableParams12 {

  case class A(var x: BigInt)

  case class B(closure: (A) => BigInt) {

    def execute(a: A): BigInt = {
      closure(a)
    }

  }

  def test(): BigInt = {
    val a = A(3)
    val b = B((capturedA: A) => {
      capturedA.x = capturedA.x + 1
      capturedA.x
    })

    b.execute(a)
    b.execute(a)
    b.execute(a)
  } ensuring(_ == 6)

}

