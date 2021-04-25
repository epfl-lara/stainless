import stainless.lang._
import stainless.annotation._
import stainless.proof._

object Zero {

  def zero1(arg: BigInt): BigInt = { 
    if(arg > 0) zero1(arg -1)
    else BigInt(0)
  }//ensuring(res => res == zero2(arg))

  def zero2(arg: BigInt): BigInt = {
    BigInt(0)
  }//ensuring(res => res == zero1(arg))
  
  @traceInduct("")
  def zero_check(arg: BigInt): Boolean = {
    zero1(arg) == zero2(arg)
  }.holds

}
