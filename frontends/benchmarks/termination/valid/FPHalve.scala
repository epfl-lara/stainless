import stainless.lang.*

def f(a: Float): Float = {
  require(!a.isNaN && 0 < a && a <= 2)
  decreases(a)
  val epsilon = 0.01
  if a < epsilon then a else f(a / 2)
}
