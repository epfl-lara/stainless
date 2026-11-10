import stainless.lang._
import stainless.math._

/** `max` and `min` on floating point numbers return NaN when either argument is NaN, and
  * order -0.0 below +0.0, as on the JVM.
  */
object FloatingPointMinMax {
  def maxNaNRight(x: Double) = { max(x, Double.NaN) }.ensuring(_.isNaN)
  def maxNaNLeft(x: Double) = { max(Double.NaN, x) }.ensuring(_.isNaN)
  def minNaNRight(x: Double) = { min(x, Double.NaN) }.ensuring(_.isNaN)
  def minNaNLeft(x: Double) = { min(Double.NaN, x) }.ensuring(_.isNaN)

  def maxNaNFloat(x: Float) = { max(x, Float.NaN) }.ensuring(_.isNaN)
  def minNaNFloat(x: Float) = { min(Float.NaN, x) }.ensuring(_.isNaN)

  def maxIsUpperBound(x: Double, y: Double) = {
    require(!x.isNaN && !y.isNaN)
    max(x, y)
  }.ensuring(r => r >= x && r >= y && (r == x || r == y))

  def minIsLowerBound(x: Float, y: Float) = {
    require(!x.isNaN && !y.isNaN)
    min(x, y)
  }.ensuring(r => r <= x && r <= y && (r == x || r == y))

  def maxOfZeros(x: Double, y: Double) = {
    require(!x.isNaN && !y.isNaN && x == 0.0 && y == 0.0 && (1 / x > 0 || 1 / y > 0))
    max(x, y)
  }.ensuring(r => 1 / r > 0)

  def minOfZeros(x: Double, y: Double) = {
    require(!x.isNaN && !y.isNaN && x == 0.0 && y == 0.0 && (1 / x < 0 || 1 / y < 0))
    min(x, y)
  }.ensuring(r => 1 / r < 0)
}
