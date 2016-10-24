import leon.lang._

object Lambdas2 {

  val init_messages = (i: BigInt) => BigInt(0)
  
  
  def smallNumbers(n: BigInt, messages: BigInt => BigInt)(i: BigInt, j: BigInt) = {
    i < n && j < n
  }

  def intForAll2(n: BigInt, m: BigInt, p: (BigInt, BigInt) => Boolean): Boolean = {
//     forall ((i: BigInt, j: BigInt) => (0 <= i && i < n && 0 <= j && j < n) ==> p(i,j))

    if (n <= 0 || m <= 0) true
    else p(n-1,m-1) && intForAll2(n-1, m, p) && intForAll2(n, m-1, p)
  }
  
  def invariant(n: BigInt, messages: BigInt => BigInt) = {
    intForAll2(n, n, smallNumbers(n, messages))
  }

  def theorem(n: BigInt) = {
    require(intForAll2(n, n, smallNumbers(n, init_messages)))
    
    invariant(n, init_messages)
  } holds
  
}
