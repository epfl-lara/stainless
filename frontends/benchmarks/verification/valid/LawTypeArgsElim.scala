import stainless.lang._
import stainless.annotation._
import stainless.proof._

object LawTypeArgsElim {
  abstract class Structure[A] {
    def doSomething(x: A, y: A): A

    @law
    def someLaw(x: A, y: A): Boolean = {
      doSomething(x, y) == doSomething(y, x)
    }
  }

  case class BigIntStructure() extends Structure[BigInt] {
    override def doSomething(x: BigInt, y: BigInt): BigInt = {
      x + y
    }

    override def someLaw(x: BigInt, y: BigInt): Boolean = {
      super.someLaw(x, y) because {
        x + y == y + x
      }
    }
  }

  def ok1[A](s: Structure[A], a: A, b: A) = {
    assert(s.someLaw(a, b))                            // valid
    assert(s.doSomething(a, b) == s.doSomething(b, a)) // valid
  }

  case class OptionStructure[A](ev: Structure[A]) extends Structure[Option[A]] {
    override def doSomething(x: Option[A], y: Option[A]): Option[A] = {
      (x, y) match {
        case (None(), None())   => None()
        case (_, None())        => None()
        case (None(), _)        => None()
        case (Some(a), Some(b)) => Some(ev.doSomething(a, b))
      }
    }

    override def someLaw(x: Option[A], y: Option[A]): Boolean = {
      super.someLaw(x, y) because {
        (x, y) match {
          case (None(), None())   => true
          case (_, None())        => true
          case (None(), _)        => true
          case (Some(a), Some(b)) => ev.someLaw(a, b)
        }
      }
    }
  }

  def ok2[A](s: Structure[Option[A]], a: Option[A], b: Option[A]) = {
    assert(s.someLaw(a, b))                            // valid
    assert(s.doSomething(a, b) == s.doSomething(b, a)) // valid
  }
}
