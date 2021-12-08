object InnerClassesInvariants1 {

  case class Ref(var value: BigInt)

  def rejected(x: Ref): Unit = {
    require(0 < ref.value && ref.value < 10)
    var y = x
    val z = y

    case class Local() {
      def smth: Unit = {
        assert(0 < x.value && x.value < 10)
        assert(0 < y.value && y.value < 10)
        assert(0 < z.value && z.value < 10)
      }
    }
    val local = Local()
    y.value = 42 // Illegal aliasing
  }
}