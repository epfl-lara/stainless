import stainless.lang._

// Same as AbstractMethodBodySpec, with a trait, a generic method, and methods
// that have only a precondition, only a postcondition, or no contract at all.
object AbstractMethodBodyTrait {
  trait Counter {
    def value: BigInt = AbstractMethodBody[BigInt]()

    def isValid: Boolean = {
      AbstractMethodBody[Boolean]()
    }.ensuring(res => res == (value >= 0))

    def add(n: BigInt): Counter = {
      require(n >= 0 && isValid)
      AbstractMethodBody[Counter]()
    }.ensuring(res => res.isValid && res.value == value + n)

    def pick[T](a: T, b: T): T = {
      AbstractMethodBody[T]()
    }.ensuring(res => res == a || res == b)
  }

  case class Simple(v: BigInt) extends Counter {
    override def value: BigInt = v

    override def isValid: Boolean = {
      v >= 0
    }.ensuring(res => res == (value >= 0))

    override def add(n: BigInt): Counter = {
      require(n >= 0 && isValid)
      Simple(v + n)
    }.ensuring(res => res.isValid && res.value == value + n)

    override def pick[T](a: T, b: T): T = {
      a
    }.ensuring(res => res == a || res == b)
  }

  def addTwice(c: Counter, n: BigInt): Counter = {
    require(n >= 0 && c.isValid)
    c.add(n).add(n)
  }.ensuring(res => res.value == c.value + 2 * n)

  def test: BigInt = {
    addTwice(Simple(1), 2).value
  }.ensuring(_ == 5)
}
