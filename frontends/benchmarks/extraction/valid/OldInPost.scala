 import stainless.lang._
 
 object Main {
   case class A(var x: BigInt)
 
   def f(a: A): BigInt = {
     a.x = a.x + 1
     a.x
  }.ensuring(_ > old(a).x)
 }
