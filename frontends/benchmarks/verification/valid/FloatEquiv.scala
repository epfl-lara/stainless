import stainless.lang.*

object FloatEquiv {
  // floats are either equal or not equal
  def floatEqOrNotEq(a: Float, b: Float): Boolean = {
    a.equiv(b) || !a.equiv(b)
  }.holds

  def doubleEqOrNotEq(a: Double, b: Double): Boolean = {
    a.equiv(b) || !a.equiv(b)
  }.holds

  // NaN is equal to NaN and minus zero is not equal to plus zero, unlike comparisons with the == operator
  def floatNaNEqNaN(): Boolean = {
    Float.NaN.equiv(Float.NaN)
  }.holds

  def doubleNaNEqNaN(): Boolean = {
    Double.NaN.equiv(Double.NaN)
  }.holds

  def floatPlusMinusZeroNonEq(): Boolean = {
    !(-0.0f.equiv(0.0f))
  }.holds

  def doublePlusMinusZeroNonEq(): Boolean = {
    !(-0.0d.equiv(0.0d))
  }.holds

  // the equiv method is an equivalence relation //
  def floatEquivReflexivity(a: Float): Boolean = {
    a.equiv(a)
  }.holds

  def floatEquivSymmetry(a: Float, b: Float): Boolean = {
    a.equiv(b) == b.equiv(a)
  }.holds

  def floatEquivTransitivity(a: Float, b: Float, c: Float): Boolean = {
    !a.equiv(b) || !b.equiv(c) || a.equiv(c)
  }.holds

  def doubleEquivReflexivity(a: Double): Boolean = {
    a.equiv(a)
  }.holds

  def doubleEquivSymmetry(a: Double, b: Double): Boolean = {
    a.equiv(b) == b.equiv(a)
  }.holds

  def doubleEquivTransitivity(a: Double, b: Double, c: Double): Boolean = {
    !a.equiv(b) || !b.equiv(c) || a.equiv(c)
  }.holds
}