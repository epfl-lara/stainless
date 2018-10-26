
object InnerClassesScope1 {
  def scope = {
    case class First(value: BigInt) {
      def makeSecond = Second(value)
    }

    case class Second(value: BigInt) {
      def makeFirst = First(value)
    }

    First(42).makeSecond.makeFirst.value
  }

  def prop = {
    assert(scope == 42)
  }
}
