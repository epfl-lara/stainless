object BadOverride1 {
  sealed abstract class Abs {
    require(x != 0)
    val x: Int
  }
  case class AbsInvalid() extends Abs {
    def x: Int = 1
  }
}
