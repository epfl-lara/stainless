
import stainless.lang._

object ST {

  case class World[A]()

  case class ST[S, A](private val runST: World[S] => (World[S], A)) {
    def map[B](f: A => B): ST[S, B] = ST { s =>
      runST(s) match {
        case (ns, a) => (ns, f(a))
      }
    }

    def flatMap[B](f: A => ST[S, B]): ST[S, B] = ST { s =>
      runST(s) match {
        case (ns, a) => f(a).runST(ns)
      }
    }
  }

  object ST {
    def pure[S, A](a: A): ST[S, A] = ST { s => (s, a) }
  }

  case class STRef[S, A](private var value: A) {
    def read: ST[S, A] = ST.pure(value)

    def write(a: A): ST[S, STRef[S, A]] =  ST { s =>
      value = a
      (s, this)
    }

    def modify(f: A => A): ST[S, STRef[S, A]] = for {
      a <- read
      v <- write(f(a))
    } yield v
  }

}

