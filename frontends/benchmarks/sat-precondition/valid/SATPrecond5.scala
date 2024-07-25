import stainless.collection._

object SATPrecond5 {
  
    def f(l1: List[BigInt], l2: List[BigInt]): BigInt = {
      require(l1.forall(y => y > 0))
      require(ListSpecs.subseq(l2, l1))
      require(l2.length < l1.length)
      42
    }
  }
