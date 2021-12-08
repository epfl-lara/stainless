object InnerClassesInvariants {

  def test1(x: BigInt): Unit = {
    val y = x
    val z = y

    case class Local()
  }

  def test2(x: BigInt): Unit = {
    require(x > 0 && x < 10)
    val y = x
    val z = y

    case class Local()
  }

  def test3(x: BigInt): Unit = {
    require(0 < x && x < 10)
    val y = x
    val z = y + 10

    case class Local() {
      def smth: Unit = {
        assert(0 < x && x < 10)
        assert(0 < y && y < 10)
        assert(10 < z && z < 20)
      }
    }
  }

  def test4(x: BigInt): Unit = {
    require(0 < x && x < 10)
    val y = x
    val z = y + 10

    case class Local() {
      val someField = y + 3
      def smth: Unit = {
        assert(0 < x && x < 10)
        assert(0 < y && y < 10)
        assert(10 < z && z < 20)
        assert(3 < someField && someField < 13)
      }
    }
  }

  def test5(x: BigInt): Unit = {
    require(0 < x && x < 10)
    val y = x
    val z = y + 10

    case class Local(w: BigInt) {
      require(w > z)
      def smth: Unit = {
        assert(0 < x && x < 10)
        assert(0 < y && y < 10)
        assert(10 < z && z < 20)
        assert(w > z)
      }
    }
  }

  def test6(x: BigInt): Unit = {
    require(0 < x && x < 10)
    val y = x
    val z = y + 10

    def nested(w: BigInt): Unit = {
      require(w < z)
      case class Local() {
        def smth: Unit = {
          assert(0 < x && x < 10)
          assert(0 < y && y < 10)
          assert(10 < z && z < 20)
          assert(w < 20)
        }
      }
    }
  }

  def test7(arr: Array[BigInt], x: Int): Unit = {
    require(0 < x && x < arr.length)
    val y = arr(x) + 42
    case class Local() {
      def smth: Unit = {
        val z = y + 10
      }
    }
  }
}