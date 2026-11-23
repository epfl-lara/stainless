import stainless.lang._

// `???` may appear in executable code as long as it is provably unreachable.
object UnimplementedUnreachable {
  def branch(x: BigInt): BigInt = {
    require(x > 0)
    if (x > 0) x else (??? : BigInt)
  }

  def matching(o: Option[BigInt]): BigInt = {
    require(o.isDefined)
    o match {
      case Some(v) => v
      case None() => (??? : BigInt)
    }
  }

  def never(x: BigInt): BigInt = {
    require(false)
    (??? : BigInt)
  }.ensuring(_ > x)

  def nothing: Nothing = {
    require(false)
    ???
  }

  def lambda(x: BigInt): BigInt => BigInt = {
    require(x > 0)
    if (x > 0) (y: BigInt) => y + x
    else (y: BigInt) => (??? : BigInt)
  }

  def local(x: BigInt): BigInt = {
    require(x > 0)
    def positive(y: BigInt): BigInt = {
      require(y > 0)
      if (y > 0) y else (??? : BigInt)
    }
    positive(x)
  }

  // No class runs the body of `area`, since the only concrete subclass overrides it
  abstract class Shape {
    def area(k: BigInt): BigInt = {
      require(k >= 0)
      if (k == 0) BigInt(0) else (??? : BigInt)
    }.ensuring(_ >= 0)
  }

  case class Point() extends Shape {
    override def area(k: BigInt): BigInt = {
      require(k >= 0)
      BigInt(0)
    }.ensuring(_ >= 0)
  }

  def test: BigInt = {
    val s: Shape = Point()
    branch(1) + matching(Some(2)) + lambda(1)(2) + local(3) + s.area(4) +
      (if (branch(1) < 0) never(1) else BigInt(0)) +
      (if (branch(1) < 0) nothing else BigInt(0))
  }
}
