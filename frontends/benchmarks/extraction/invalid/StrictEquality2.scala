object StrictEquality2:
  case class Box(a: Any) derives CanEqual

  sealed abstract class Shape derives CanEqual
  case class Circle(r: BigInt) extends Shape
  case class Tagged(tag: (BigInt, Any)) extends Shape
