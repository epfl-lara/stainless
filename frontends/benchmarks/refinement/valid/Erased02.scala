import stainless.lang._

case class A(x: BigInt) {

  def f() = {
    erased val a = x + 1
    val res: {res : BigInt with res >= a} = x + 2
  }
}
