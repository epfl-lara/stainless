import stainless.lang._

object i1159 {

  def foo1(): Unit = {
    var i = 1234
    def isZero = i == 0

    def inside: Unit = {
      require(i <= 2000)
      i = 0
    }.ensuring(_ =>
      isZero
    )

    inside
  }

  def foo2(): Unit = {
    var i: BigInt = 0
    var j: BigInt = 1
    def isAnswerToLife = i + j == 42

    def inside(wantAnswer: Boolean): Unit = {
      if (wantAnswer) {
        i = 22
        j = 20
      } else {
        i = 0xbadca11
        j = 0
      }
    }.ensuring(_ =>
      wantAnswer ==> isAnswerToLife
    )

    // We don't know what we want
    (inside(true), inside(false))
  }

  def foo3(): Unit = {
    var i: BigInt = 0
    var j: BigInt = 1
    def evenSumIsEven = {
      require(i % 2 == 0 && j % 2 == 0)
      (i + j) % 2 == 0
    }

    def inside(newI: BigInt, newJ: BigInt): Unit = {
      i = newI
      j = newJ
    }.ensuring(_ =>
      (newI % 2 == 0 && newJ % 2 == 0) ==> evenSumIsEven
    )
  }

}
