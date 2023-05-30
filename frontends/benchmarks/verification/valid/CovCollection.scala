import stainless.annotation._
import stainless.covcollection._
import ListOps._

object CovCollection {
  def zipWith[A,B,C](f: (A,B) => C)(l1: List[A], l2: List[B]): List[C] = {
    require(l1.blength == l2.blength)
    (l1, l2) match {
      case (Nil, Nil) => Nil
      case (a :: as, b :: bs) => f(a,b) :: zipWith(f)(as, bs)
    }
  }

  // Unsealed hierarchy
  trait UnsealedSeal {
    def x: BigInt
  }
  case class EmpressLeakySeal(x: BigInt, y: BigInt) extends UnsealedSeal
  case class EmperorLeakySeal(x: BigInt, y: BigInt) extends UnsealedSeal

  def test1(s1: EmpressLeakySeal, s2: EmperorLeakySeal): Unit = {
    val l1 = s1 :: s2 :: Nil
    val l2 = s2 :: s1 :: Nil
    assert(sum(l1.map(_.x)) == sum(l2.map(_.x)))
  }

  def separate(seals: List[UnsealedSeal]): (List[EmpressLeakySeal], List[EmperorLeakySeal], List[UnsealedSeal]) = seals match {
    case Nil => (Nil, Nil, Nil)
    case (s: EmpressLeakySeal) :: t =>
      val (a2, b2, c2) = separate(t)
      (s :: a2, b2, c2)
    case (s: EmperorLeakySeal) :: t =>
      val (a2, b2, c2) = separate(t)
      (a2, s :: b2, c2)
    case s :: t =>
      val (a2, b2, c2) = separate(t)
      (a2, b2, s :: c2)
  }

  @ghost
  def test2(s1: EmpressLeakySeal, s2: EmperorLeakySeal, s3: UnsealedSeal): Unit = {
    require(s3 match {
      case _: EmpressLeakySeal => false
      case _: EmperorLeakySeal => false
      case _ => true
    })
    val (a, b, c) = separate(s1 :: s2 :: s3 :: Nil)
    assert(a == s1 :: Nil)
    assert(b == s2 :: Nil)
    assert(c == s3 :: Nil)
  }

  @ghost
  def test3(s1: EmpressLeakySeal, s2: EmperorLeakySeal, s3: UnsealedSeal): Unit = {
    require(s3 match {
      case _: EmpressLeakySeal => false
      case _: EmperorLeakySeal => false
      case _ => true
    })
    val (a, b, c) = separate(List(s1, s2, s3))
    assert(a == List(s1))
    assert(b == List(s2))
    assert(c == List(s3))
  }

  def separate(s: UnsealedSeal): (Option[EmpressLeakySeal], Option[EmperorLeakySeal]) = s match {
    case s: EmpressLeakySeal => (Some(s), None)
    case s: EmperorLeakySeal => (None, Some(s))
    case _ => (None, None)
  }

  @ghost
  def test4(s1: EmpressLeakySeal, s2: EmperorLeakySeal, s3: UnsealedSeal): Unit = {
    require(s3 match {
      case _: EmpressLeakySeal => false
      case _: EmperorLeakySeal => false
      case _ => true
    })
    val (a1, b1) = separate(s1)
    assert(a1 == Some(s1))
    assert(b1 == None)
    val (a2, b2) = separate(s2)
    assert(a2 == None)
    assert(b2 == Some(s2))
    val (a3, b3) = separate(s3)
    assert(a3 == None)
    assert(b3 == None)
  }

}