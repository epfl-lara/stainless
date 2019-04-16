import stainless.lang._

object InnerClasses1 {

  abstract class Test[A] {
    def something: BigInt
  }

   def foo(x: BigInt, l: BigInt): Test[Boolean] = {
     require(l > 1)
     case class FooBarBaz[B](a: BigInt, b: B) extends Test[B] {
       def something: BigInt = a + l
     }
     FooBarBaz(x, true)
   }

   def prop = {
     foo(1, 2).something == 3
   }.holds

}
