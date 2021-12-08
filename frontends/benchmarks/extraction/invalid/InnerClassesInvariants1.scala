object InnerClassesInvariants1 {

  def rejected(x: BigInt): Unit = {
    require(0 < x && x < 10)
    var y = x
    val z = y

    case class Local() {
      def smth: Unit = {
        assert(0 < x && x < 10)
        assert(0 < y && y < 10) // Cannot close over mutable y
        assert(0 < z && z < 10)
      }
    }
  }
}