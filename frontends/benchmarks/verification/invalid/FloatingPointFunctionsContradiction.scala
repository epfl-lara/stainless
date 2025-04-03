import stainless.math.*
import stainless.lang.*

// since some properties of transcendental functions are axiomatized, we check that false is not implied
object FloatingPointFunctionsContradiction {
  def testSin(d: Double) = { sin(d) }.ensuring(false)
  def testAsin(d: Double) = { asin(d) }.ensuring(false)
  def testCos(d: Double) = { cos(d) }.ensuring(false)
  def testAcos(d: Double) = { acos(d) }.ensuring(false)
  def testTan(d: Double) = { tan(d) }.ensuring(false)
  def testAtan(d: Double) = { atan(d) }.ensuring(false)
  def testPow(d1: Double, d2: Double) = { pow(d1, d2) }.ensuring(false)
  def testExp(d: Double) = { exp(d) }.ensuring(false)
  def testAtan2(d1: Double, d2: Double) = { atan2(d1, d2) }.ensuring(false)
}
