import stainless.lang._
object MixinSuperCalls {
  trait Base { def f(x: BigInt): BigInt = x }
  trait Inc extends Base { override def f(x: BigInt): BigInt = super.f(x) + 1 }
  trait Dbl extends Base { override def f(x: BigInt): BigInt = super.f(x) * 2 }
  abstract class Mid extends Base with Inc
  case class Top() extends Mid with Dbl { override def f(x: BigInt): BigInt = super.f(x) + 100 }
  case class Plain() extends Mid
  trait Box[T] { def get(t: T): T = t }
  trait Wrap[T] extends Box[T] { override def get(t: T): T = super.get(t) }
  case class IntBox() extends Box[BigInt] with Wrap[BigInt]
  def test: Unit = {
    assert(Top().f(1) == 104)
    assert(Plain().f(1) == 2)
    assert(IntBox().get(3) == 3)
  }
}
