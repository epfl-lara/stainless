import stainless.annotation._

object i1274a {
  @extern
  def f(x: BigInt): Unit = {
    var t = x
    t += 1
    // This require is not properly extracted into a spec (due to having impure constructs before)
    // It will disappear because bodies of @extern functions are removed
    // As this is in general not the behavior one expects, we should reject the program.
    require(t >= 10)
  }
}