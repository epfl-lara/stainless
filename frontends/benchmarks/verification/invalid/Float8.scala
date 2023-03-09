object Float8 {
  final case class Float8(mant: Int, exp: Int) {
    require(0 <= mant && mant <= 15 && 0 <= exp && exp <= 15)
    def value: Int = mant << exp

    def +(y: Float8): Float8 = {
      val x = this
      if (x.exp <= y.exp) {
        val shift = y.exp - x.exp
        val mant = (x.mant >> shift) + y.mant
        if (mant < 16) Float8(mant, y.exp)
        else {
          val exp1 = y.exp + 1
          if (exp1 < 16) Float8(mant / 2, y.exp + 1)
          else Float8(15, 15)
        }
      }
      else y + x
    }
  }

  def plusAssoc(x: Float8, y: Float8, z: Float8): Unit = {
    ()
  }.ensuring(_ => x + (y + z) == (x + y) + z)
}