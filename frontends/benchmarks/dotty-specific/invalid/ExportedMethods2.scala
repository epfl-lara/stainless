object ExportedMethods2 {
  import ExportedMethodsExt.SimpleCounter.*

  case class Wrapper(base: Base) {
    export base.*

    def addWith(y: BigInt): Unit = {
      add(y) // invalid
    }
  }
}