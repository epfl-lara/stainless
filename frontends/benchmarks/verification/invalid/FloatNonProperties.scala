import stainless.lang.*

object FloatNonProperties {
  // floats with '<' are not connected //
  def floatLessThanNotConnected(a: Float, b: Float): Boolean = {
    a == b || a < b || b < a
  }.holds

  def doubleLessThanNotConnected(a: Double, b: Double): Boolean = {
    a == b || a < b || b < a
  }.holds

  // floats with '<=' are not reflexive, antisymmetric, or connected //
  def floatReflexivity(a: Float): Boolean = {
    a <= a
  }.holds

  def floatAntisymmetry(a: Float, b: Float): Boolean = {
    a <= b || b <= a
  }.holds

  def floatAntisymmetry2(a: Float, b: Float): Boolean = {
    a <= b || a >= b
  }.holds

  def floatLessEqualsConnected(a: Float, b: Float): Boolean = {
    a <= b || b <= a
  }.holds

  def doubleReflexivity(a: Double): Boolean = {
    a <= a
  }.holds

  def doubleAntisymmetry(a: Double, b: Double): Boolean = {
    a <= b || b <= a
  }.holds

  def doubleAntisymmetry2(a: Double, b: Double): Boolean = {
    a <= b || a >= b
  }.holds

  def doubleLessEqualsConnected(a: Double, b: Double): Boolean = {
    a <= b || b <= a
  }.holds

  // finite floats are not associative //
  def finiteFloatAdditionAssociativity(a: Float, b: Float, c: Float): Boolean = {
    require(a.isFinite)
    require(b.isFinite)
    require(c.isFinite)
    (a + b) + c == a + (b + c)
  }.holds

  def finiteFloatMultiplicationAssociativity(a: Float, b: Float, c: Float): Boolean = {
    require(a.isFinite)
    require(b.isFinite)
    require(c.isFinite)
    (a * b) * c == a * (b * c)
  }.holds

  def finiteDoubleAdditionAssociativity(a: Double, b: Double, c: Double): Boolean = {
    require(a.isFinite)
    require(b.isFinite)
    require(c.isFinite)
    (a + b) + c == a + (b + c)
  }.holds

  def finiteDoubleMultiplicationAssociativity(a: Double, b: Double, c: Double): Boolean = {
    require(a.isFinite)
    require(b.isFinite)
    require(c.isFinite)
    (a * b) * c == a * (b * c)
  }.holds

  // some arithmetic simplification valid for reals are invalid for floats //
  def finiteFloatAddSubtract(a: Float, b: Float): Boolean = {
    require((a + b).isFinite)
    a + b - b == a
  }.holds

  def finiteFloatMultiplyDivide(a: Float, b: Float): Boolean = {
    require ((a * b).isFinite)
    a * b / b == a
  }.holds

  def finiteDoubleAddSubtract(a: Double, b: Double): Boolean = {
    require((a + b).isFinite)
    a + b - b == a
  }.holds

  def finiteDoubleMultiplyDivide(a: Double, b: Double): Boolean = {
    require((a * b).isFinite)
    a * b / b == a
  }.holds
}