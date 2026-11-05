import stainless.lang.*

object AnyEquality4:
  def set(s: Set[Any]): Boolean = s.contains(1)

  def map(m: Map[Any, BigInt]): BigInt = m(1)

  def literal(x: Any): Boolean = x match
    case 5 => true
    case _ => false
