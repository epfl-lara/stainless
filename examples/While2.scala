//Test should fail because decreases in condition

import stainless.annotation._
import stainless.collection._
import stainless.lang._

object While {

  def fi(fi: BigInt, fj: BigInt, fk: BigInt): BigInt = {
    var i = fi
    var j = fj
    var k = fk
    
    while(
      decreases(k)
      (i <= 100) && (j <= k)
    ){
      decreases(k-i-j)   
      i = j
      j = i+1
      k = k-1
    }

    i+j+k
  }
    
}

