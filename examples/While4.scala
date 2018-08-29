import stainless.annotation._
import stainless.collection._
import stainless.lang._

object While {

  def fi(fi: BigInt): BigInt = {
    require(fi >= 0)
    var i = fi
    
    (while(i < 10 && i > 0){
      decreases(i)
      i = i - 1
    }) invariant (i >= 0)

    i
  }
    
}

