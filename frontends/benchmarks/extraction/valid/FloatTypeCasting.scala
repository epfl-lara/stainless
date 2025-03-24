object FloatTypeCasting {
  def testImplicitCasting() = {
    val b: Byte = 1
    val s: Short = 2
    val i: Int = 3
    val l: Long = 4
    val f: Float = 5
    val fb: Float = b
    val fs: Float = s
    @annotation.nowarn("cat=deprecation") // deprecated since precision may be lost
    val fi: Float = i
    @annotation.nowarn("cat=deprecation")
    val fl: Float = l
    val db: Double = b
    val ds: Double = s
    val di: Double = i
    @annotation.nowarn("cat=deprecation")
    val dl: Double = l
    val df: Double = f
  }

  def testExplicitCasting() = {
    val b: Byte = 1
    val s: Short = 2
    val i: Int = 3
    val l: Long = 4
    val f: Float = 5
    val fb: Float = b.toFloat
    val fs: Float = s.toFloat
    val fi: Float = i.toFloat
    val fl: Float = l.toFloat
    val db: Double = b.toDouble
    val ds: Double = s.toDouble
    val di: Double = i.toDouble
    val dl: Double = l.toDouble
    val df: Double = f.toDouble
  }
}
