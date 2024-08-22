object ImplicitArguments {
  abstract class X {
    implicit val x: BigInt
  }

  def f(implicit sender: BigInt) = ()

  abstract class B extends X {
    def g(implicit sender: BigInt) = {
      f(x)
    }
  }

  implicit class Toto(val i: BigInt) {
    def add(j: BigInt) = i + j
  }

  def test(i: BigInt) = i.add(BigInt(2))
}
