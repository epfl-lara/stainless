
import stainless.lang._

object Enums1 {

  enum Option[+T] {
    case Some(x: T) extends Option[T]
    case None       extends Option[Nothing]
  }

}
