import stainless.lang._
object GenericOutersInherited {
  // Member classes of subclasses can extend those of generic ancestors, which the subclasses instantiate
  trait Values[V] {
    abstract class Value {
      def get: V
      final def same(v: V): Boolean = get == v
    }
    case class Const(v: V) extends Value { def get: V = v }
    final def const(v: V): Value = Const(v)
  }

  trait IntValues extends Values[BigInt] {
    case class Neg(e: Value) extends Value {
      def get: BigInt = -e.get
      def twice: BigInt = this.get * 2
    }
    final def neg(v: BigInt): Neg = Neg(const(v))
  }

  case object intValues extends IntValues

  def isNeg(l: IntValues, e: l.Value): Boolean = e match {
    case l.Neg(_) => true
    case _ => false
  }

  def inherited: Unit = {
    val n = intValues.Neg(intValues.Const(3))
    assert(n.get == -3)
    assert(n.twice == -6)
    assert(n.same(-3))
    assert(intValues.neg(1).get == -1)
    assert(isNeg(intValues, intValues.neg(1)))
    assert(!isNeg(intValues, intValues.const(1)))
  }
}
