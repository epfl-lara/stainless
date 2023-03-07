import stainless.lang._
import stainless.annotation._

object i1379g {

  trait Animal
  case class Cow(id: BigInt) extends Animal

  sealed abstract class List[+A] {
    def :: [B >: A](elem: B): List[B] = new ::(elem, this)
  }
  final case class ::[+A](first: A, next: List[A]) extends List[A]
  case object Nil extends List[Nothing]

  // It would be quite ironic for Seal to be non-sealed...
  sealed trait Seal
  case class EmpressSeal(name: String) extends Seal
  case class EmperorSeal(name: String) extends Seal

  def groupedConcreteUnsealed(xs: List[Animal]): List[List[Animal]] = {
    decreases(xs)
    xs match {
      case Nil => Nil
      case a1 :: a2 :: rest => (a1 :: a2 :: Nil) :: groupedConcreteUnsealed(rest)
      case a1 :: Nil => (a1 :: Nil) :: Nil
    }
  }

  def groupedConcreteSealed(xs: List[Seal]): List[List[Seal]] = {
    decreases(xs)
    xs match {
      case Nil => Nil
      case a1 :: a2 :: rest => (a1 :: a2 :: Nil) :: groupedConcreteSealed(rest)
      case a1 :: Nil => (a1 :: Nil) :: Nil
    }
  }

  def groupedAbstract[A](xs: List[A]): List[List[A]] = {
    decreases(xs)
    xs match {
      case Nil => Nil
      case a1 :: a2 :: rest => (a1 :: a2 :: Nil) :: groupedAbstract(rest)
      case a1 :: Nil => (a1 :: Nil) :: Nil
    }
  }

  @ghost
  def testConcreteUnsealed(a1: Animal, a2: Animal, a3: Animal, a4: Animal): Unit = {
    assert(groupedConcreteUnsealed(a1 :: a2 :: a3 :: a4 :: Nil) == (a1 :: a2 :: Nil) :: (a3 :: a4 :: Nil) :: Nil)
    assert(groupedConcreteUnsealed(a1 :: a2 :: a3 :: Nil) == (a1 :: a2 :: Nil) :: (a3 :: Nil) :: Nil)
    assert(groupedConcreteUnsealed(a1 :: Nil) == (a1 :: Nil) :: Nil)
    assert(groupedConcreteUnsealed(Nil) == Nil)
  }

  def testConcreteSealed(a1: Seal, a2: Seal, a3: Seal, a4: Seal): Unit = {
    assert(groupedConcreteSealed(a1 :: a2 :: a3 :: a4 :: Nil) == (a1 :: a2 :: Nil) :: (a3 :: a4 :: Nil) :: Nil)
    assert(groupedConcreteSealed(a1 :: a2 :: a3 :: Nil) == (a1 :: a2 :: Nil) :: (a3 :: Nil) :: Nil)
    assert(groupedConcreteSealed(a1 :: Nil) == (a1 :: Nil) :: Nil)
    assert(groupedConcreteSealed(Nil) == Nil)
  }

  def testAbstract[A](a1: A, a2: A, a3: A, a4: A): Unit = {
    assert(groupedAbstract(a1 :: a2 :: a3 :: a4 :: Nil) == (a1 :: a2 :: Nil) :: (a3 :: a4 :: Nil) :: Nil)
    assert(groupedAbstract(a1 :: a2 :: a3 :: Nil) == (a1 :: a2 :: Nil) :: (a3 :: Nil) :: Nil)
    assert(groupedAbstract(a1 :: Nil) == (a1 :: Nil) :: Nil)
    assert(groupedAbstract(Nil) == Nil)
  }
}