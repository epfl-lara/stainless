object ADTInitialization1 {
  abstract class Pair {
    val x: Int
    val y: Int
  }

  case class Balanced(x: Int = 20, y: Int = 80) extends Pair {
    require(
      0 <= x && x <= 100 &&
      0 <= y && y <= 100 &&
      x + y == 100
    )
  }

  case class Imbalanced(x: Int = 20, y: Int = 81) extends Pair {
    require(
      0 <= x && x <= 100 &&
      0 <= y && y <= 100 &&
      x + y != 100
    )
  }
}
