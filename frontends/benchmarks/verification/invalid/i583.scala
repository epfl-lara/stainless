import stainless.lang.*

object i583:

  sealed abstract class T

  case class A(x: Option[A]) extends T

  def neverSome(t: T): Boolean = {
    t match
      case A(Some(_)) => false
      case _ => true
  }.holds
