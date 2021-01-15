import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.proof._
import stainless.lang.StaticChecks._

object UpCounter {
  final case class UpCounter(var i: BigInt, var oldI: BigInt) extends AnyHeapRef  
  {
    def valid: Boolean = {
      reads(Set(this))
      oldI <= i
    }
  
    def init(v: BigInt): Unit = {
      reads(Set(this))
      require(0 <= v)
      modifies(Set(this))
      i = v
      oldI = v
    } ensuring(_ => valid)
    
    def inc: Unit = {
      reads(Set(this))
      require(valid)
      modifies(Set(this))
      i = i + 1
    } ensuring(_ => valid)

    def incBy(k: BigInt): Unit = {
      reads(Set(this))
      require(0 <= k && valid)
      modifies(Set(this))
      i = i + k
    } ensuring(_ => valid)

    def get: BigInt = {      
      reads(Set(this))
      require(valid)
      i
    } ensuring(_ => valid)
  }

  @extern
  def main(args: Array[String]): Unit = {
    val c = UpCounter(BigInt(0), BigInt(0))
    c.init(1)
    c.inc
    println("counter is: " + c)
    c.inc
    println(c.get)
  }
  
}
