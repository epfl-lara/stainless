package boxMutation3
import stainless.lang._
import stainless.annotation._

object A:
  @mutable
  case class Box(var value: Int){
    def valid: Boolean = value >= 0
    def update(v: Int with v >= 0): Unit = {
      require(valid)
      value = v
    }.ensuring(_ => valid)
  }
  def test1(b: Box with b.valid): Unit = {
    require(b.value == 1)
    assert(b.value == 1)
    b.update(10)
    assert(b.value == 10)
  }

  def test2(): Unit = {
    val b: Box with b.valid = Box(1)
    assert(b.value == 1)
    b.update(10)
    assert(b.value == 10)
  }