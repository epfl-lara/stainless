object HigherOrderFunctionsMutableParams14 {

  case class A(var x: BigInt)

  case class B(closure: (A) => BigInt, var a: A) {

    def execute(): BigInt = {
      closure(a)
    }

  }

  def closure(a: A): BigInt = {
    a.x = a.x + 1
    a.x
  }

  def test(): BigInt = {
    val b = B(closure _, A(3))

    b.execute()
    b.execute()
    b.execute()
  } ensuring(_ == 6)

}

