package boxMutation4
import stainless.lang._
import stainless.annotation._

object A:
  @mutable
  case class Box(var value: BigInt, val max: BigInt with max >= 0){
    def valid: Boolean = value >= 0
    def update(v: BigInt with v >= 0): Unit = {
      require(valid)
      value = v
    }.ensuring(_ => valid)
    def add(v: BigInt with 0 <= v && this.value + v <= this.max): Unit = {
      require(valid)
      value = value + v
    }
  }
  def test1(b: Box with b.valid): Unit = {
    require(b.value == 1)
    require(b.max == 100)
    assert(b.value == 1)
    b.add(9)
    assert(b.value == 10)
  }