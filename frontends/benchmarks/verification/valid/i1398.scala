object i1398 {
  def plusOne: BigInt => BigInt  = _ + 1

  def plusTwo: BigInt => BigInt = plusOne.andThen(plusOne)

  def test1(x: BigInt): Unit = {
    assert(plusTwo(x) == x + 2)
  }

  val minus1 = (x: BigInt) => x - 1
  val twice = (x: BigInt) => 2 * x
  val composed = minus1 compose twice compose plusOne
  val andThened = minus1 andThen twice andThen plusOne

  def test2(x: BigInt): Unit = {
    assert(composed(x) == 2 * (x + 1) - 1)
    assert(andThened(x) == (x - 1) * 2 + 1)
  }

  // if only time could be duplicated as such!
  def dup[A] = (x: A) => (x, x)
  def dupdup[A] = (x: (A, A)) => (dup(x._1), dup(x._1))
  def dupdupdupdupAndThened[A] = dup[A] andThen dupdup[A]
  def dupdupdupdupComposed[A] = dupdup[A] compose dup[A]

  def test3[A](x: A): Unit = {
    assert(dupdupdupdupAndThened(x) == dupdupdupdupComposed(x))
    assert(dupdupdupdupAndThened(x) == ((x, x), (x, x)))
  }
}