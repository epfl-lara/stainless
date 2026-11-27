import stainless.lang._

// Two independent covariant hierarchies of the same shape. Each class is a constructor of the
// shared `Object` sort, so the conditions about one hierarchy shouldn't unroll the other.
object IndependentHierarchies {
  object pa {
    sealed abstract class Opt[+T]
    case class Som[+T](v: T) extends Opt[T]
    case object Non extends Opt[Nothing]

    sealed abstract class Lst[+T] {
      def find(p: T => Boolean): Opt[T] = {
        this match {
          case Nl => Non
          case Cns(h, t) => if (p(h)) Som(h) else t.find(p)
        }
      }.ensuring { res => res match {
        case Som(r) => p(r)
        case Non => true
      }}
    }
    case object Nl extends Lst[Nothing]
    final case class Cns[+A](first: A, next: Lst[A]) extends Lst[A]
  }

  object pb {
    sealed abstract class Opt[+T]
    case class Som[+T](v: T) extends Opt[T]
    case object Non extends Opt[Nothing]

    sealed abstract class Lst[+T] {
      def find(p: T => Boolean): Opt[T] = {
        this match {
          case Nl => Non
          case Cns(h, t) => if (p(h)) Som(h) else t.find(p)
        }
      }.ensuring { res => res match {
        case Som(r) => p(r)
        case Non => true
      }}
    }
    case object Nl extends Lst[Nothing]
    final case class Cns[+A](first: A, next: Lst[A]) extends Lst[A]
  }

  def both(a: pa.Lst[BigInt], b: pb.Lst[BigInt]): Unit = {
    a.find(_ > 0) match {
      case pa.Som(x) => assert(x > 0)
      case pa.Non => ()
    }
    b.find(_ < 0) match {
      case pb.Som(y) => assert(y < 0)
      case pb.Non => ()
    }
  }
}
