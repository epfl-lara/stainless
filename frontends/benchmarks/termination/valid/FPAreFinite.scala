import stainless.lang.*

object FPAreFinite {
  // https://github.com/apache/spark/blob/7ce639e04383074f9e2458054a14fcf6331981b1/mllib/src/main/scala/org/apache/spark/mllib/util/MLUtils.scala#L46
  lazy val EPSILON = {
    var eps = 1.0
    (while ((1.0 + (eps / 2.0)) != 1.0) {
      decreases(eps)
      eps /= 2.0
    }).invariant(!eps.isNaN && 1.0 >= eps && eps > 0.0)
    eps
  }
}
