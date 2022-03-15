import stainless.lang._

object i1159a {

  def foo(): Unit = {
    var i = 0
    def isZero = i == 0

    def inside: Unit = {
      require(i <= 10)
      i += 1
    }.ensuring(_ =>
      isZero
    )

    inside
  }

}
