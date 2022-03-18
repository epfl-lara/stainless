import stainless.lang._

object i1159b {

  def foo(): Unit = {
    var i = 0
    def isZero = i == 0

    def inside: Unit = {
      require(i <= 10)
    }.ensuring(_ =>
      isZero // Reported as invalid, even though we never modify i (due to the hoisting of `inside`)
    )

    inside
  }

}
