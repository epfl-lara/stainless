/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package math

import stainless.annotation.*

/** Unsigned integers: `UByte` (8 bits), `UShort` (16 bits), `UInt` (32 bits)
 *  and `ULong` (64 bits).
 *
 *  Each type is an opaque alias of the signed primitive type of the same width,
 *  which holds the same bits. Stainless maps these types to its native unsigned
 *  bitvector types, so the definitions below are `@ignore`d by the verifier and
 *  by GenC (where they become `uint8_t`, ..., `uint64_t`). They provide the
 *  executable (JVM) semantics, which are the semantics used for verification:
 *
 *    - arithmetic (`+`, `-`, `*`, unary `-`) and `<<` wrap around modulo `2^N`;
 *    - comparisons, `/` and `%` are unsigned; `/` and `%` by zero throw an
 *      [[ArithmeticException]];
 *    - the shift amount is read as an unsigned value, and shifting by `N` or
 *      more bits yields `0`; `>>>` is a logical shift (there is no `>>`: an
 *      arithmetic shift has no meaning on unsigned values, and the C `>>` on
 *      unsigned types is logical, so either semantics would surprise some
 *      users);
 *    - `toUByte`, `toUShort`, `toUInt` and `toULong` zero-extend or truncate an
 *      unsigned value, sign-extend or truncate a `Byte`, `Short`, `Int` or
 *      `Long`, then reinterpret the bits as unsigned, and take a `BigInt`
 *      modulo `2^N`; unsigned literals are written with these conversions
 *      (`200.toUByte`), which Stainless extracts as literals when in range;
 *    - `toByte`, `toShort`, `toInt` and `toLong` zero-extend or truncate an
 *      unsigned value, then reinterpret the bits as signed (see below).
 *
 *  For instance:
 *  {{{
 *  200.toUByte.toInt == 200
 *  200.toUByte.toByte == -56
 *  }}}
 *
 *  As the values are represented by signed primitives on the JVM, `toString`
 *  (and string interpolation) shows the signed value: use `toStringUnsigned`
 *  instead, which Stainless treats as an uninterpreted function (see
 *  [[UnsignedStrings]]). For the same reason, an unsigned value can only be
 *  compared with `==` to a value of the same type (the Scala compiler rejects
 *  `x == 200` for `x: UByte`, which would be `false` on the JVM even if `x` is
 *  `200`): write `x == 200.toUByte` instead.
 */
@library
@ignore
object Unsigned:

  opaque type UByte = Byte
  opaque type UShort = Short
  opaque type UInt = Int
  opaque type ULong = Long

  // In this object, the unsigned types are their underlying signed types, whose members (`+`, `<`, `toInt`,
  // ...) are the signed operations: the operations below must not rely on them when the sign matters.
  private def u8(x: Byte): Int = java.lang.Byte.toUnsignedInt(x)
  private def u16(x: Short): Int = java.lang.Short.toUnsignedInt(x)
  private def u32(x: Int): Long = java.lang.Integer.toUnsignedLong(x)

  object UByte:
    val MinValue: UByte = 0
    val MaxValue: UByte = -1

    extension (x: UByte)
      def unary_~ : UByte = (~x).toByte
      def unary_- : UByte = (-x).toByte
      def +(y: UByte): UByte = (x + y).toByte
      def -(y: UByte): UByte = (x - y).toByte
      def *(y: UByte): UByte = (x * y).toByte
      def /(y: UByte): UByte = (u8(x) / u8(y)).toByte
      def %(y: UByte): UByte = (u8(x) % u8(y)).toByte
      def <(y: UByte): Boolean = u8(x) < u8(y)
      def <=(y: UByte): Boolean = u8(x) <= u8(y)
      def >(y: UByte): Boolean = u8(x) > u8(y)
      def >=(y: UByte): Boolean = u8(x) >= u8(y)
      def |(y: UByte): UByte = (x | y).toByte
      def &(y: UByte): UByte = (x & y).toByte
      def ^(y: UByte): UByte = (x ^ y).toByte
      def <<(y: UByte): UByte = if u8(y) >= 8 then 0 else (x << u8(y)).toByte
      def >>>(y: UByte): UByte = if u8(y) >= 8 then 0 else (u8(x) >>> u8(y)).toByte

      def toUShort: UShort = u8(x).toShort
      def toUInt: UInt = u8(x)
      def toULong: ULong = u8(x).toLong

      def toByte: Byte = x
      def toShort: Short = u8(x).toShort
      def toInt: Int = u8(x)
      def toLong: Long = u8(x).toLong

      def toBigInt: BigInt = BigInt(u8(x))
      def toStringUnsigned: String = u8(x).toString

  object UShort:
    val MinValue: UShort = 0
    val MaxValue: UShort = -1

    extension (x: UShort)
      def unary_~ : UShort = (~x).toShort
      def unary_- : UShort = (-x).toShort
      def +(y: UShort): UShort = (x + y).toShort
      def -(y: UShort): UShort = (x - y).toShort
      def *(y: UShort): UShort = (x * y).toShort
      def /(y: UShort): UShort = (u16(x) / u16(y)).toShort
      def %(y: UShort): UShort = (u16(x) % u16(y)).toShort
      def <(y: UShort): Boolean = u16(x) < u16(y)
      def <=(y: UShort): Boolean = u16(x) <= u16(y)
      def >(y: UShort): Boolean = u16(x) > u16(y)
      def >=(y: UShort): Boolean = u16(x) >= u16(y)
      def |(y: UShort): UShort = (x | y).toShort
      def &(y: UShort): UShort = (x & y).toShort
      def ^(y: UShort): UShort = (x ^ y).toShort
      def <<(y: UShort): UShort = if u16(y) >= 16 then 0 else (x << u16(y)).toShort
      def >>>(y: UShort): UShort = if u16(y) >= 16 then 0 else (u16(x) >>> u16(y)).toShort

      def toUByte: UByte = x.toByte
      def toUInt: UInt = u16(x)
      def toULong: ULong = u16(x).toLong

      def toByte: Byte = x.toByte
      def toShort: Short = x
      def toInt: Int = u16(x)
      def toLong: Long = u16(x).toLong

      def toBigInt: BigInt = BigInt(u16(x))
      def toStringUnsigned: String = u16(x).toString

  object UInt:
    val MinValue: UInt = 0
    val MaxValue: UInt = -1

    extension (x: UInt)
      def unary_~ : UInt = ~x
      def unary_- : UInt = -x
      def +(y: UInt): UInt = x + y
      def -(y: UInt): UInt = x - y
      def *(y: UInt): UInt = x * y
      def /(y: UInt): UInt = java.lang.Integer.divideUnsigned(x, y)
      def %(y: UInt): UInt = java.lang.Integer.remainderUnsigned(x, y)
      def <(y: UInt): Boolean = java.lang.Integer.compareUnsigned(x, y) < 0
      def <=(y: UInt): Boolean = java.lang.Integer.compareUnsigned(x, y) <= 0
      def >(y: UInt): Boolean = java.lang.Integer.compareUnsigned(x, y) > 0
      def >=(y: UInt): Boolean = java.lang.Integer.compareUnsigned(x, y) >= 0
      def |(y: UInt): UInt = x | y
      def &(y: UInt): UInt = x & y
      def ^(y: UInt): UInt = x ^ y
      def <<(y: UInt): UInt = if u32(y) >= 32 then 0 else x << y
      def >>>(y: UInt): UInt = if u32(y) >= 32 then 0 else x >>> y

      def toUByte: UByte = x.toByte
      def toUShort: UShort = x.toShort
      def toULong: ULong = u32(x)

      def toByte: Byte = x.toByte
      def toShort: Short = x.toShort
      def toInt: Int = x
      def toLong: Long = u32(x)

      def toBigInt: BigInt = BigInt(u32(x))
      def toStringUnsigned: String = java.lang.Integer.toUnsignedString(x)

  object ULong:
    val MinValue: ULong = 0L
    val MaxValue: ULong = -1L

    extension (x: ULong)
      def unary_~ : ULong = ~x
      def unary_- : ULong = -x
      def +(y: ULong): ULong = x + y
      def -(y: ULong): ULong = x - y
      def *(y: ULong): ULong = x * y
      def /(y: ULong): ULong = java.lang.Long.divideUnsigned(x, y)
      def %(y: ULong): ULong = java.lang.Long.remainderUnsigned(x, y)
      def <(y: ULong): Boolean = java.lang.Long.compareUnsigned(x, y) < 0
      def <=(y: ULong): Boolean = java.lang.Long.compareUnsigned(x, y) <= 0
      def >(y: ULong): Boolean = java.lang.Long.compareUnsigned(x, y) > 0
      def >=(y: ULong): Boolean = java.lang.Long.compareUnsigned(x, y) >= 0
      def |(y: ULong): ULong = x | y
      def &(y: ULong): ULong = x & y
      def ^(y: ULong): ULong = x ^ y
      def <<(y: ULong): ULong = if java.lang.Long.compareUnsigned(y, 64L) >= 0 then 0L else x << y
      def >>>(y: ULong): ULong = if java.lang.Long.compareUnsigned(y, 64L) >= 0 then 0L else x >>> y

      def toUByte: UByte = x.toByte
      def toUShort: UShort = x.toShort
      def toUInt: UInt = x.toInt

      def toByte: Byte = x.toByte
      def toShort: Short = x.toShort
      def toInt: Int = x.toInt
      def toLong: Long = x

      def toBigInt: BigInt = if x >= 0 then BigInt(x) else BigInt(x) + (BigInt(1) << 64)
      def toStringUnsigned: String = java.lang.Long.toUnsignedString(x)

  // Conversions from the signed types: sign-extension or truncation, then reinterpretation of the bits.
  // Unsigned literals are written with them, e.g. `200.toUByte`.

  extension (x: Byte)
    def toUByte: UByte = x
    def toUShort: UShort = x.toShort
    def toUInt: UInt = x.toInt
    def toULong: ULong = x.toLong

  extension (x: Short)
    def toUByte: UByte = x.toByte
    def toUShort: UShort = x
    def toUInt: UInt = x.toInt
    def toULong: ULong = x.toLong

  extension (x: Int)
    def toUByte: UByte = x.toByte
    def toUShort: UShort = x.toShort
    def toUInt: UInt = x
    def toULong: ULong = x.toLong

  extension (x: Long)
    def toUByte: UByte = x.toByte
    def toUShort: UShort = x.toShort
    def toUInt: UInt = x.toInt
    def toULong: ULong = x

  // Conversions from `BigInt`: the value modulo 2^N, as for `BigInt.toInt`
  extension (x: BigInt)
    def toUByte: UByte = x.toByte
    def toUShort: UShort = x.toShort
    def toUInt: UInt = x.toInt
    def toULong: ULong = x.toLong

/** The conversions of unsigned values to their decimal representation, which
 *  Stainless treats as uninterpreted functions: Stainless extracts
 *  `x.toStringUnsigned` as a call to the function of this object for the type
 *  of `x`, so that it can be used in verified code (but nothing is known about
 *  its result, except that it only depends on `x`).
 */
@library
object UnsignedStrings:
  import Unsigned.*

  @extern def ubyteToString(x: UByte): String = x.toStringUnsigned
  @extern def ushortToString(x: UShort): String = x.toStringUnsigned
  @extern def uintToString(x: UInt): String = x.toStringUnsigned
  @extern def ulongToString(x: ULong): String = x.toStringUnsigned
