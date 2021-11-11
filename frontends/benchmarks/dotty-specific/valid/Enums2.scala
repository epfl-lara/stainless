
import stainless.lang._

object Enums2 {

  enum Option[+T] {
    case Some(x: T) extends Option[T]
    case None       extends Option[Nothing]
  }
  import Option._

  def map[A, B](o: Option[A])(f: A => B): Option[B] = o match {
    case Some(a) => Some(f(a))
    case None => None
  }

  def simple: Boolean = {
    map(Some(21))(_ * 2) == Some(42)
  }.holds
}
