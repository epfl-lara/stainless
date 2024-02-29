object ExportedMethods3 {
  import ExportedMethodsExt.CounterWithInvariant.*

  case class Wrapper(base: Base) {
    export base.*

    def addWith(y: BigInt): Unit = {
      x = y
    }
  }
}