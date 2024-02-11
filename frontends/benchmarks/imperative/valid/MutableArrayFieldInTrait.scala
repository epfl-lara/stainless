import stainless.annotation._
import stainless.lang._
import StaticChecks._

object MutableArrayFieldInTrait {
  case class Buffer(arr: Array[Byte])

  @mutable
  trait MyTrait {
    val buf: Buffer

    final def modify: Unit = {
      if (buf.arr.length >= 10) buf.arr(0) = 1
    }
  }
  case class MyClass(buf: Buffer) extends MyTrait

  def modify(buf: Buffer, i: Int): Unit = {
    require(0 <= i && i < buf.arr.length)
    buf.arr(i) = 42
  }

  def test(mt: MyTrait, i: Int, j: Int, k: Int): Unit = {
    require(0 <= i && i < mt.buf.arr.length)
    require(0 <= j && j < mt.buf.arr.length)
    require(0 <= k && k < mt.buf.arr.length)
    require(i != j && j != k && i != k)
    val oldi = mt.buf.arr(i)
    modify(mt.buf, j)
    mt.buf.arr(k) = 24
    assert(mt.buf.arr(i) == oldi)
    assert(mt.buf.arr(j) == 42)
    assert(mt.buf.arr(k) == 24)
  }
}