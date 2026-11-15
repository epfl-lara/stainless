import stainless.collection.*
import stainless.lang.*

object i583:

  sealed abstract class T

  case class A(x: Option[A]) extends T

  case class B(args: List[T]) extends T

  def identity(t: T): T =
    t match
      case A(Some(_)) => t
      case _ => t

  def identity2(t: T): T =
    t match
      case B(_ :: Nil()) => t
      case _ => identity(t)

  def isA(a: A): Boolean =
    true

  def innerIsA(t: T): Boolean = {
    t match
      case A(Some(a)) => isA(a)
      case _ => true
  }.holds

  def someOrNone(a: A): Boolean = {
    a match
      case A(Some(_)) => a.x.isDefined
      case A(None()) => a.x.isEmpty
  }.holds
