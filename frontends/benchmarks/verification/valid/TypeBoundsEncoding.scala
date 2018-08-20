
import stainless.lang._

object TypeBoundsEncoding {

  abstract class Dummy[M] {
    def dummy: M
  }

  case class Const[A](value: A)

  case class ConstDummy[X](x: X) extends Dummy[Const[X]] {
    def dummy: Const[X] = Const(x)
  }

  // ----------------------------------------

  // case class Box(value: BigInt)

  // case class Test() extends Dummy[Box] {
  //   def dummy = Box(42)
  // }

  // ----------------------------------------

  // case class Box[A](x: A) {
  //   def size: BigInt = 1
  // }

  // def test[B](b: B): BigInt = {
  //   if (b.isInstanceOf[Box[_]]) {
  //     b.asInstanceOf[Box[_]].size
  //   } else {
  //     0
  //   }
  // }

}
