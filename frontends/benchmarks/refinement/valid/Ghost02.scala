import language.experimental.qualifiedTypes.silent
import stainless.annotation.ghost
import stainless.lang._

case class A(x: BigInt) {

  def f() = {
    @ghost val a = x + 1
    val res: {res : BigInt with res >= a} = x + 2
  }
}