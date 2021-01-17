import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.proof._
import stainless.lang.StaticChecks._

object BigIntArray {
  final case class SArray[T](var content: List[T]) extends AnyHeapRef
  {
    def fill(n: BigInt)(default: T): Unit = {
      // should become a constructor eventually instead of a method
      reads(Set(this))
      require(0 <= n)
      modifies(Set(this))
      content = List.fill(n)(default)
    }
  
    def apply(i: BigInt): T = {
      reads(Set(this))
      require(0 <= i && i < content.size)
      content(i)
    }

    def update(i: BigInt, v: T): Unit = {
      reads(Set(this))
      require(0 <= i && i < content.size)
      modifies(Set(this))
      content = content.updated(i, v)
    }
  }

  @extern
  def main(args: Array[String]): Unit = {
    val s = SArray[String](List[String]())
    s.fill(5)("")
    s(3) = "s3"
    s(0) = "s0"
    s(2) = "s2"
    s(4) = "s4"
    println("SArray is: " + s)
  }
}
