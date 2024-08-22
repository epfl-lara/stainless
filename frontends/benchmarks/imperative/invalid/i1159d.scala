import stainless.lang._

object i1159d {

  def foo(): Unit = {
    var i: BigInt = 0
    var j: BigInt = 1
    def evenSumIsEven = {
      require(i % 2 == 0 && j % 2 == 0)
      (i + j) % 2 == 0
    }

    def inside: Unit = {
      i = 41
      j = 0
   }.ensuring(_ =>
      evenSumIsEven
    )

    inside
  }

}
