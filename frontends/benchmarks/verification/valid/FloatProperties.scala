import stainless.lang.*

object FloatProperties {
  // floats are either equal or not equal
  def floatEqOrNotEq(a: Float, b: Float): Boolean = {
    a == b || a != b
  }.holds

  // floats with '<' form a strict partial order; total order for finite floats //
  def floatIrreflexivity(a: Float): Boolean = {
    !(a < a)
  }.holds

  def floatAssymetry(a: Float, b: Float): Boolean = {
    !(a < b && b < a)
  }.holds

  def floatAssymetry2(a: Float, b: Float): Boolean = {
    !(a < b && a > b)
  }.holds

  def floatTransitivity(a: Float, b: Float, c: Float): Boolean = {
    !(a < b) || !(b < c) || (a < c)
  }.holds

  def finiteFloatsLessThanConnected(a: Float, b: Float): Boolean = {
    require(a.isFinite)
    require(b.isFinite)
    a == b || a < b || b < a
  }.holds

  def doubleIrreflexivity(a: Double): Boolean = {
    !(a < a)
  }.holds

  def doubleAssymetry(a: Double, b: Double): Boolean = {
    !(a < b && b < a)
  }.holds

  def doubleAssymetry2(a: Double, b: Double): Boolean = {
    !(a < b && a > b)
  }.holds

  def doubleTransitivity(a: Double, b: Double, c: Double): Boolean = {
    !(a < b) || !(b < c) || (a < c)
  }.holds

  def finiteDoublesLessThanConnected(a: Double, b: Double): Boolean = {
    require(a.isFinite)
    require(b.isFinite)
    a == b || a < b || b < a
  }.holds

  // finite floats with '<=' form a total order //
  def finiteFloatsReflexivity(a: Float): Boolean = {
    require(a.isFinite)
    a <= a
  }.holds

  def finiteFloatsAntisymmetry(a: Float, b: Float): Boolean = {
    require(a.isFinite)
    require(b.isFinite)
    a <= b || b <= a
  }.holds

  def finiteFloatsAntisymmetry2(a: Float, b: Float): Boolean = {
    require(a.isFinite)
    require(b.isFinite)
    a <= b || a >= b
  }.holds

  def finiteFloatsTransitivity(a: Float, b: Float, c: Float): Boolean = {
    require(a.isFinite)
    require(b.isFinite)
    require(c.isFinite)
    !(a <= b) || !(b <= c) || a <= c
  }.holds

  def finiteFloatsLessEqualsConnected(a: Float, b: Float): Boolean = {
    require(a.isFinite)
    require(b.isFinite)
    a <= b || b <= a
  }.holds

  def finiteDoublesReflexivity(a: Double): Boolean = {
    require(a.isFinite)
    a <= a
  }.holds

  def finiteDoublesAntisymmetry(a: Double, b: Double): Boolean = {
    require(a.isFinite)
    require(b.isFinite)
    a <= b || b <= a
  }.holds

  def finiteDoublesAntisymmetry2(a: Double, b: Double): Boolean = {
    require(a.isFinite)
    require(b.isFinite)
    a <= b || a >= b
  }.holds

  def finiteDoublesTransitivity(a: Double, b: Double, c: Double): Boolean = {
    require(a.isFinite)
    require(b.isFinite)
    require(c.isFinite)
    !(a <= b) || !(b <= c) || a <= c
  }.holds

  def finiteDoublesLessEqualsConnected(a: Double, b: Double): Boolean = {
    require(a.isFinite)
    require(b.isFinite)
    a <= b || b <= a
  }.holds

  // finite floats are commutative //
  def finiteFloatAdditionCommutativity(f1: Float, f2: Float): Boolean = {
    require(f1.isFinite)
    require(f2.isFinite)
    f1 + f2 == f2 + f1
  }.holds

  def finiteFloatMultiplicationCommutativity(f1: Float, f2: Float): Boolean = {
    require(f1.isFinite)
    require(f2.isFinite)
    f1 * f2 == f2 * f1
  }.holds

  // it takes z3 several minutes to show commutativity for doubles
//  def finiteDoubleAdditionCommutativity(f1: Double, f2: Double): Boolean = {
//    require(f1.isFinite)
//    require(f2.isFinite)
//    f1 + f2 == f2 + f1
//  }.holds
//
//  def finiteDoubleMultiplicationCommutativity(f1: Double, f2: Double): Boolean = {
//    require(f1.isFinite)
//    require(f2.isFinite)
//    f1 * f2 == f2 * f1
//  }.holds
}