 object Chain3{

  import stainless.lang._
  import stainless.annotation._
  import stainless.collection._
  import stainless.math.{max,min,abs}

  def f(n: BigInt): BigInt = {
    require(n >= BigInt(0))
    //decreases(n,0) <- chain in f
    decreases(n,1)
    if(n == BigInt(0)){
      BigInt(0)
    } else {
      g(n-2)
    }   
  } 

  def g(n: BigInt): BigInt = {
    require(n >= BigInt(0))
    //decreases(n+1,1) <- chain in f
    decreases(n+2,0)
    if(n == BigInt(0)){
      BigInt(0)
    } else {
      f(n+1)
    }
  }

}