import stainless.math.BitVectors._

// `BigInt` literals converted to bitvectors (`bigIntToBV`), signed and unsigned, in range.
object BitVectors4 {

  def test1 = {
    val a: UInt8 = BigInt(200)
    assert(a > (100: UInt8))
  }

  def test2 = {
    val min: UInt8 = BigInt(0)
    val max: UInt8 = BigInt(255)
    assert(min < max)
  }

  def test3 = {
    val a: Int8 = BigInt(-100)
    assert(a < (0: Int8))
  }

  def test4 = {
    val min: Int8 = BigInt(-128)
    val max: Int8 = BigInt(127)
    assert(min < max)
  }

  def test5 = {
    val a: UInt100 = BigInt("1267650600228229401496703205375") // 2^100 - 1
    assert(a == max[UInt100])
  }

}
