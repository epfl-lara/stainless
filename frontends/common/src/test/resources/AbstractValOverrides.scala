
object AbstractValsOverrideOk {

  abstract class Abs {
    val x: Int
    val y: Int
    def z: Int
  }

  abstract class Sub extends Abs {
    def z: Int = 42
  }

  case class Ok(x: Int, y: Int) extends Sub
}

object AbstractValsOverrideBad {

  abstract class Abs {
    val x: Int
    val y: Int
    def z: Int
  }

  abstract class Sub extends Abs {
    val x: Int = 1
  }

  case class Ok(y: Int, z: Int) extends Sub

  case class Bad() extends Sub {
    def y: Int = 1
    def z: Int = 2
  }
}

