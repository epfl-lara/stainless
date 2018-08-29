import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.math._

object While {

  def fi(fi: BigInt, fj: BigInt, fk: BigInt): BigInt = {
    var i = fi
    var j = fj
    var k = fk
    
    (while((i <= 100) && (j <= k)){
      decreases(max(k-i-j+100,0))   
      val s = i
      i = j
      j = s+1
      k = k-1
    }) invariant(max(k-i-j+100,0) >= 0)

    i+j+k
  }

}

