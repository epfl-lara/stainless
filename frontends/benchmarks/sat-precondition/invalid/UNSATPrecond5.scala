import stainless.collection._

object SATPrecond5 {
  
    def f(l1: List[BigInt], l2: List[BigInt]): BigInt = {
      require(l1.forall(y => y > 0))
      val z = l1.length
      require(l2.length < l1.length)
      require(z < 2)
      require(l2.length > 10)
      42
    }
  }
