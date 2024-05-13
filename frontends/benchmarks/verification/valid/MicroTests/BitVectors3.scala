import stainless.math.BitVectors._

object BitVectors3 {

  def test1(x: UInt42): Unit = {
    assert(x.toSigned[Int42].toUnsigned[UInt42] == x)
  }

  def test2(a: Array[Boolean], x: UInt8): Unit = {
    require(a.length > 1 && a(1) && x == (1: UInt8))

    assert(a(x.widen[UInt32].toSigned[Int32].toInt))
  }

  def test3: Unit = {
    val x: UInt8 = 255
    assert(x.toSigned[Int8] == (-1: Int8))
  }

  def test4(z: Int4): Unit = {
    val x1: UInt8 = 145
    val x2: Int8 = x1.toSigned[Int8] // conversion from unsigned to signed ints

    // Bitvectors can be compared to literal constants, which are encoded as a bitvector of the same
    // type as the left-hand-side bitvector.
    // In the line below, `-111` get encoded internally as an `Int8`
    assert(x2 == (-111: Int8))

    // In Stainless internals, `Int8` and `Byte` are the same type, for not for the surface language,
    // so `toByte` allows to go from `Int8` to `Byte`.
    // Similarly, we support `toShort`, `toInt`, `toLong` for conversions
    // respectively from `Int16` to `Short`, `Int32` to `Int`, `Int64` to `Long`,
    // and `fromByte`, `fromShort`, `fromInt`, `fromLong` for the other direction
    val x3: Byte = x2.toByte
    assert(x3 == (-111: Byte))

    // Unsigned ints can be cast to larger unsigned types
    val x4: UInt12 = x1.widen[UInt12]
    assert(x4 == (145: UInt12))

    // or truncated to smaller unsigned types.
    val x5: UInt4 = x1.narrow[UInt4]
    assert(x5 == (1: UInt4)) // 145 % 2^4 == 1

    // Signed ints can also be cast to larger signed types (using sign extension)
    val x6: Int8 = 120
    val x7: Int12 = x6.widen[Int12]
    assert(x7 == (120: Int12))

    // and cast to smaller signed types.
    // This corresponds to extracting the low-end of the bit representation
    // (see `extract` here http://smtlib.cs.uiowa.edu/logics-all.shtml)
    val x8: Int4 = x6.narrow[Int4]
    assert(x8 == (-8: Int4))

    // the `toByte`, `toShort`, `toInt`, and `toLong` methods described above
    // can be used on any bitvector type. For signed integers, this corresponds
    // to a narrowing or a widening operation dependending on the bitvector size.
    // For unsigned integers, this corresponds to first doing a widering/narrowing
    // operation, and then applying `toSigned`
    val x9: UInt2 = 3
    assert(x9.toInt == x9.widen[UInt32].toSigned[Int32].toInt)

    // the BitVectors library also provide constants for maximum and minimum values
    assert(max[Int8] == (127: Int8))
    assert(min[Int8] == (-128: Int8))
  }

}
