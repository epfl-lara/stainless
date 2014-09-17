import leon.lang._

object Monads2 {
  abstract class Option[T]
  case class Some[T](t: T) extends Option[T]
  case class None[T]() extends Option[T]

  def flatMap[T,U](opt: Option[T], f: T => Option[U]): Option[U] = opt match {
    case Some(x) => f(x)
    case None() => None()
  }

  def associative_law[T,U,V](opt: Option[T], f: T => Option[U], g: U => Option[V]): Boolean = {
    flatMap(flatMap(opt, f), g) == flatMap(opt, (x: T) => flatMap(f(x), g))
  }.holds

  def left_unit_law[T,U](x: T, f: T => Option[U]): Boolean = {
    flatMap(Some(x), f) == f(x)
  }.holds

  def right_unit_law[T,U](opt: Option[T]): Boolean = {
    flatMap(opt, (x: T) => Some(x)) == opt
  }.holds

  /*
  def associative_induct[T,U,V](opt: Option[T], f: T => Option[U], g: U => Option[V]): Boolean = {
    opt match {
      case Some(x) => associative(opt)

    }
  }
  */
}

// vim: set ts=4 sw=4 et:
