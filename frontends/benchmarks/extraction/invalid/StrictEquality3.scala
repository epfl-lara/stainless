object StrictEquality3:
  case class Point(x: BigInt, y: BigInt)

  given CanEqual[Point, Point] = CanEqual.derived

  given CanEqual[Any, Any] = CanEqual.derived
