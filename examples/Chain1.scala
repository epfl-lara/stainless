 /*
   Considering the chain as starting at f, 
   we reproduce the chain strategy on decreases.
   We add 1 as a shift to ensure positivity.
 */

 object Chain1{

  import stainless.lang._
  import stainless.annotation._
  import stainless.collection._
  import stainless.math.{max,min,abs}

  def f(n: BigInt): BigInt = {
    require(n >= BigInt(0))
    decreases(n+4,0)
    if(n == BigInt(0)){
      BigInt(0)
    } else {
      g(n+3)
    }   
  } 

  def g(n: BigInt): BigInt = {
    require(n >= BigInt(0))
    decreases(n,2)
    if(n == BigInt(0)){
      BigInt(0)
    } else {
      h(n-2)
    }
  }

  def h(n: BigInt): BigInt = {
    require(n >= BigInt(0))
    decreases(n+2,1)
    if(n == BigInt(0)){
      BigInt(0)
    } else {
      f(n-2)
    }
  }

}