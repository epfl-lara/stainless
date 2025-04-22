import stainless.lang.*

object FloatNonProperties {
  // floats with '<' are not connected //
  def floatLessThanNotConnected(a: Float, b: Float): Boolean = {
    a == b || a < b || b < a
  }

  def doubleLessThanNotConnected(a: Double, b: Double): Boolean = {
    a == b || a < b || b < a
  }

  // floats with '<=' are not reflexive, antisymmetric, or connected //
  def floatReflexivity(a: Float): Boolean = {
    a <= a
  }

  def floatAntisymmetry(a: Float, b: Float): Boolean = {
    a <= b || b <= a
  }

  def floatAntisymmetry2(a: Float, b: Float): Boolean = {
    a <= b || a >= b
  }

  def floatLessEqualsConnected(a: Float, b: Float): Boolean = {
    a <= b || b <= a
  }

  def doubleReflexivity(a: Double): Boolean = {
    a <= a
  }

  def doubleAntisymmetry(a: Double, b: Double): Boolean = {
    a <= b || b <= a
  }

  def doubleAntisymmetry2(a: Double, b: Double): Boolean = {
    a <= b || a >= b
  }

  def doubleLessEqualsConnected(a: Double, b: Double): Boolean = {
    a <= b || b <= a
  }

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

  def test(a1: Float, b1: Float,
           a2: Double, b2: Double,
           a3: Float,
           a4: Float, b4: Float,
           a5: Float, b5: Float,
           a6: Float, b6: Float,
           a7: Double,
           a8: Double, b8: Double,
           a9: Double, b9: Double,
           a10: Double, b10: Double,
           a11: Float, b11: Float, c11: Float,
           a12: Float, b12: Float, c12: Float,
           a13: Double, b13: Double, c13: Double,
           a14: Double, b14: Double, c14: Double,
          ): Boolean = {
    require(a11.isFinite && b11.isFinite && c11.isFinite)
    require(a12.isFinite && b12.isFinite && c12.isFinite)
//    require(a13.isFinite && b13.isFinite && c13.isFinite)
//    require(a14.isFinite && b14.isFinite && c14.isFinite)
    floatLessThanNotConnected(a1, b1)
    || doubleLessThanNotConnected(a2, b2)
    || floatReflexivity(a3)
    || floatAntisymmetry(a4, b4)
    || floatAntisymmetry2(a5, b5)
    || floatLessEqualsConnected(a6, b6)
    || doubleReflexivity(a7)
    || doubleAntisymmetry(a8, b8)
    || doubleAntisymmetry2(a9, b9)
    || doubleLessEqualsConnected(a10, b10)
    || finiteFloatAdditionAssociativity(a11, b11, c11)
    || finiteFloatMultiplicationAssociativity(a12, b12, c12)
//    || finiteDoubleAdditionAssociativity(a13, b13, c13)
//    || finiteDoubleMultiplicationAssociativity(a14, b14, c14)
  }.holds
}