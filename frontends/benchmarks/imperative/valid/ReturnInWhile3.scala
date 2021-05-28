import stainless.lang._

object ReturnInWhile3 {
  def f: Unit = {
    var x = 1000
    (while (true) {
      decreases(x)
      x = stainless.math.max(x / 2 - 100 / x, 0)

      if (x == 0) return
    }).weakInvariant(0 < x && x <= 1000) // true except possibly after a return
  }
}
