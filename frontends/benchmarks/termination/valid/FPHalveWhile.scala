import stainless.lang.*

def f(a: Float): Float = {
  require(!a.isNaN && 0 < a && a <= 2)
  decreases(a)
  val epsilon = 0.01
  var b = a
  (while (b >= epsilon) {
    decreases(b)
    b = b / 2
  }).invariant(!b.isNaN && 0 < b && b <= a)
  b
}