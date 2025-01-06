object ExportedMethods1 {
  case class Counter(var x: BigInt) {
    def add(y: BigInt): Unit = {
      require(y >= 0)
      x += y
    }
  }

  case class Base(cnt: Counter) {
    export cnt.*
  }

  case class Wrapper(base: Base) {
    export base.*

    def addWith(y: BigInt): Unit = {
      add(y) // invalid
    }
  }
}