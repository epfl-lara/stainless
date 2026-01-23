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
          ): Boolean = {
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
  }.holds
}