// Disabled until https://github.com/epfl-lara/stainless/issues/241 is fixed
//
// import stainless.lang._

// object InnerClasses2 {

//   abstract class Test {
//     def something: BigInt
//   }

//   def foo[A](x: A, l: BigInt): Test = {
//     require(l > 1)
//     def bar[B](y: B, m: BigInt): Test = {
//       require(m > 2)
//       def baz[C](z: C, o: BigInt): Test = {
//         require(o > 3)
//         case class FooBarBaz(a: A, b: B, c: C) extends Test {
//           def something: BigInt = l + m + o
//         }
//         FooBarBaz(x, y, z)
//       }
//       baz[BigInt](3, 4)
//     }
//     bar[BigInt](2, 3)
//   }
// }
