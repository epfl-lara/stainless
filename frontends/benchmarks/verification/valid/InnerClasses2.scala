
import stainless.lang._

object InnerClasses2 {

  // abstract class Foo {
  //   def something: BigInt
  // }

  // def foo[A](x: A, l: BigInt): BigInt = {
  //   require(l > 1)
  //   def bar[B](y: B, m: BigInt): BigInt = {
  //     require(m > 2)
  //     def baz[C](z: C, o: BigInt): BigInt = {
  //       require(o > 3)
  //       case class FooBarBaz(a: A, b: B, c: C) extends Foo {
  //         def something: BigInt = l + m + o
  //       }
  //       FooBarBaz(x, y, z).something
  //     }
  //     baz[BigInt](3, 4)
  //   }
  //   bar[BigInt](2, 3)
  // }

  // def test = {
  //   foo[BigInt](1, 2) == BigInt(9)
  // }.holds

  val placeholder = true.holds

}
