import stainless.lang._
import stainless.annotation._

object ArrayParamMutation1 {

  def update(a: Array[BigInt]): Unit = {
    require(a.length > 0)
    a(0) = 10
  }

  @pure
  def f(): BigInt = {
    val a = Array.fill(10)(BigInt(0))
    update(a)
    a(0)
  } ensuring(res => res == 10)

}
