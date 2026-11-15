import stainless.collection.*
import stainless.lang.*

object i1024b:

  def size(l: List[BigInt]): BigInt = {
    l match
      case Nil() => BigInt(0)
      case h :: t => 1 + size(t)
  }.ensuring(res => res == l.size)

  def sizeConsFirst[T](l: List[T]): BigInt = {
    l match
      case h :: t => 1 + sizeConsFirst(t)
      case Nil() => BigInt(0)
  }.ensuring(res => res == l.size)

  def firstTwo[T](l: List[T]): Option[(T, T)] = {
    l match
      case a :: b :: t => Some((a, b))
      case a :: Nil() => None()
      case Nil() => None()
  }.ensuring(res => res.isDefined == (l.size >= 2))
