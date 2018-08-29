import stainless.annotation._
import stainless.collection._
import stainless.math._
import stainless.lang._

object While {

  def test(_x: BigInt) = {
    var x = _x

    while (x > 0) {
      decreases(max(x,0))
      x = x - 1
    }
  
  }

}

