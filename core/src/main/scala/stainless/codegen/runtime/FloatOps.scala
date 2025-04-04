package stainless.codegen.runtime

object FloatOps {
  def isPositive(f: Float): Boolean = f > +0f || f.equals(+0f)

  def isPositive(d: Double): Boolean = d > +0d || d.equals(+0d)

  def isNegative(f: Float): Boolean = f < -0f || f.equals(-0f)

  def isNegative(d: Double): Boolean = d < -0d || d.equals(-0d)
}
