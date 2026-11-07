object StrictEquality1:
  def anys(): Boolean =
    val a: Any = (5: Byte)
    val b: Any = 5
    a == b

  def mixed(a: Any): Boolean = a == 5

  def param[T](x: T, y: T): Boolean = x == y

  case class Point(x: BigInt, y: BigInt)

  def points(p: Point, q: Point): Boolean = p == q
