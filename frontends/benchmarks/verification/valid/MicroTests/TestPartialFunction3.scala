
import stainless.lang._

object partialfunctionext {

  def test1 = PartialFunction[Option[String], Int] {
    case Some(str) => 42
  }

  def test2 = PartialFunction[Option[String], Int] {
    case Some(str) => 42
    case None() => 0
  }

  def test3 = PartialFunction[Option[String], Int] {
    case _ => 42
  }

  def foo(y: BigInt): Boolean = {
    require(y != 0)

    val f = PartialFunction[BigInt, BigInt] {
      case x if x != 0 => (2 * x) / x
    }

    assert(!f.pre(0))
    assert(f.pre(1))
    f(y) == 2
  }.holds

  def bar(pf: BigInt ~> BigInt, y: BigInt): BigInt = {
    require(pf.pre(y))
    pf(y)
  }

  def baz(y: BigInt): Boolean = {
    require(y > 0)

    val res = bar(PartialFunction[BigInt, BigInt] {
      case n if n > 0 => n
      case n if n == 0 => n + 1
    }, y)

    res > 0
  }.holds

}
