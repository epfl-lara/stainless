import stainless.lang.*

object FloatNonAssociativity {
  // finite floats are not associative //
  def finiteFloatAdditionAssociativity(a: Float, b: Float, c: Float): Boolean = {
    require(a.isFinite)
    require(b.isFinite)
    require(c.isFinite)
    (a + b) + c == a + (b + c)
  }

  def finiteFloatMultiplicationAssociativity(a: Float, b: Float, c: Float): Boolean = {
    require(a.isFinite)
    require(b.isFinite)
    require(c.isFinite)
    (a * b) * c == a * (b * c)
  }

  // it takes z3 several minutes to disprove commutativity for doubles
//  def finiteDoubleAdditionAssociativity(a: Double, b: Double, c: Double): Boolean = {
//    require(a.isFinite)
//    require(b.isFinite)
//    require(c.isFinite)
//    (a + b) + c == a + (b + c)
//  }
//
//  def finiteDoubleMultiplicationAssociativity(a: Double, b: Double, c: Double): Boolean = {
//    require(a.isFinite)
//    require(b.isFinite)
//    require(c.isFinite)
//    (a * b) * c == a * (b * c)
//  }

  def test(a1: Float, b1: Float, c1: Float,
           a2: Float, b2: Float, c2: Float,
           a3: Double, b3: Double, c3: Double,
           a4: Double, b4: Double, c4: Double,
          ): Boolean = {
    require(a1.isFinite && b1.isFinite && c1.isFinite)
    require(a2.isFinite && b2.isFinite && c2.isFinite)
//    require(a3.isFinite && b3.isFinite && c3.isFinite)
//    require(a4.isFinite && b4.isFinite && c4.isFinite)
    finiteFloatAdditionAssociativity(a1, b1, c1)
    || finiteFloatMultiplicationAssociativity(a2, b2, c2)
//    || finiteDoubleAdditionAssociativity(a3, b3, c3)
//    || finiteDoubleMultiplicationAssociativity(a4, b4, c4)
  }.holds
}