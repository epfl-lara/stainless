
import stainless.lang._
import stainless.annotation._

object HeapProjectionsExample {
  final case class Box(var value: BigInt) extends AnyHeapRef

  def read(x: Box): BigInt = {
    reads(Set(x))
    modifies(Set())
    x.value
  }

  def readInvariant(x: Box, y: Box): Unit = {
    reads(Set(x, y))
    modifies(Set(y))
    require(!(x.refEq(y)))
    val x1 = read(x)
    y.value += 1
    val x2 = read(x)
    assert(x1 == x2)
  }

  def write(x: Box, y: Box): Unit = {
    reads(Set(x, y))
    modifies(Set(x))
    x.value += 1
  }

  def writeInvariant(x: Box, y: Box): Unit = {
    reads(Set(x, y))
    modifies(Set(x))
    require(!(x.refEq(y)))
    val y1 = y.value
    write(x, y)
    val y2 = y.value
    assert(y1 == y2)
  }


  @extern
  def readExt(x: Box): BigInt = {
    reads(Set(x))
    modifies(Set())
    x.value
  }

  def readInvariantExt(x: Box, y: Box): Unit = {
    reads(Set(x, y))
    modifies(Set(y))
    require(!(x.refEq(y)))
    val x1 = readExt(x)
    y.value += 1
    val x2 = readExt(x)
    assert(x1 == x2)
  }

  @extern
  def writeExt(x: Box, y: Box): Unit = {
    reads(Set(x, y))
    modifies(Set(x))
    x.value += 1
  }

  def writeInvariantExt(x: Box, y: Box): Unit = {
    reads(Set(x, y))
    modifies(Set(x))
    require(!(x.refEq(y)))
    val y1 = y.value
    writeExt(x, y)
    val y2 = y.value
    assert(y1 == y2)
  }
}
