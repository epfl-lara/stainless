object BadOverride2 {
  sealed abstract class Abs {
    val y: Int
  }
  case class AbsInvalid() extends Abs {
    lazy val y: Int = 2
  }
}
