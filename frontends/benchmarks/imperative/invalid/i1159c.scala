import stainless.lang._

object i1159c {

  def foo(): Unit = {
    var i: BigInt = 0
    var j: BigInt = 1
    def isAnswerToLife = i + j == 42

    def inside: Unit = {
      require(i <= 10)
      i = 41
      j = 0
      // Oh no, we are off-by-one to the answer to life :(
    }.ensuring(_ =>
      isAnswerToLife
    )

    inside
  }

}
