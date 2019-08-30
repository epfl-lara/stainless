
object InnerClassesScope2 {
  def scope = {
    case class First(value: BigInt) {
      def makeSecond = Second(value)
    }

    def middle: First = bottom(true)

    case class Second(value: BigInt) {
      def makeFirst = First(value)
    }

    def bottom(x: Boolean): First = if (x) First(42) else middle

    middle.makeSecond.makeFirst.value
  }

  def prop = {
    assert(scope == 42)
  }
}
