import stainless.lang._
import stainless.math._

// Variant of Float8, but with a packed representation
object PackedFloat8 {
  final case class PackedFloat8(underlying: Byte) {
    def mant: Int = ((underlying) >> 4) & 0xF

    def exp: Int = underlying & 0xF

    def value: Int = mant << exp

    def +(y: PackedFloat8): PackedFloat8 = {
      val x = this
      decreases(if (x.exp <= y.exp) 0 else 1)
      if (x.exp <= y.exp) {
        val shift = y.exp - x.exp
        val mant = (x.mant >> shift) + y.mant
        if (mant < 16) PackedFloat8(mant, y.exp)
        else {
          val exp1 = y.exp + 1
          if (exp1 < 16) PackedFloat8(mant / 2, y.exp + 1)
          else PackedFloat8(15, 15)
        }
      }
      else y + x
    }
  }

  object PackedFloat8 {
    def apply(mant: Int, exp: Int): PackedFloat8 = {
      require(0 <= mant && mant <= 15)
      require(0 <= exp && exp <= 15)
      val underlying = ((mant << 4) | exp) & 0xFF
      PackedFloat8(wrapping(underlying.toByte))
    }.ensuring(res => res.mant == mant && res.exp == exp)
  }

  def plusAssoc(x: PackedFloat8, y: PackedFloat8, z: PackedFloat8): Unit = {
    ()
  }.ensuring(_ => x + (y + z) == (x + y) + z)
}
