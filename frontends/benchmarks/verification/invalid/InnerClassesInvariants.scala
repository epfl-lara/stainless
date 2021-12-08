object InnerClassesInvariants {
  def invalid(x: BigInt): Unit = {
    require(0 < x && x < 10)
    val y = x
    val z = y

    case class Local() {
      def smth: Unit = {
        assert(0 < x && x < 10)
        assert(y < 5) // invalid
      }
    }
  }
}