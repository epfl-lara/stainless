import stainless.lang.*

private val pio2_lo: Double = java.lang.Double.longBitsToDouble(0x3c91a62633145c07L)
def zzz(x: Long): Double = {
  pio2_lo
}.ensuring(res => res.isZero)