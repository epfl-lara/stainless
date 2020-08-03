object ValOverrideAbstract {
  sealed abstract class AAA {
    def f: BigInt
  }

  case class BBB() extends AAA {
    val f: BigInt = 0
  }
}
