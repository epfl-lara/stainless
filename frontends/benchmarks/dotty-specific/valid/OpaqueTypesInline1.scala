import stainless.lang._

// When the enclosing object of an inlined method declares an opaque type alias,
// Dotty's inliner materializes that object as local proxies in the inlined code
// (`val $proxy1: Lib.type{type Positive = BigInt} = Lib.$asInstanceOf[...]`,
// `val Lib$_this = $proxy1`) and casts value arguments to `A & A[Lib := $proxy1]`.
// This is the shape of `Try.flatMap` in the Stainless library, in a user object.
object OpaqueTypesInline1 {
  object Lib {
    opaque type Positive = BigInt

    sealed abstract class Try[T] {
      inline def flatMap[U](f: T => Try[U]): Try[U] = this match {
        case Success(t) => f(t)
        case Failure(exc) => Failure(exc)
      }
    }
    case class Success[T](t: T) extends Try[T]
    case class Failure[T](exc: BigInt) extends Try[T]
  }

  import Lib._

  def g(x: Try[BigInt]): Try[BigInt] = {
    x.flatMap(y => Success(y + 1))
  }.ensuring(res => res match {
    case Success(r) => x match {
      case Success(y) => r == y + 1
      case _ => false
    }
    case Failure(_) => x.isInstanceOf[Failure[BigInt]]
  })
}
