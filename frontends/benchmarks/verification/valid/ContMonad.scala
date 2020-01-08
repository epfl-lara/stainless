import stainless.lang._
import stainless.annotation._

object ContMonad {

  case class Cont[R, A](runCont: (A => R) => R) {
    @inline
    def map[B](f: A => B): Cont[R, B] = Cont { (k: B => R) =>
      runCont((a: A) => k(f(a)))
    }

    @inline
    def flatMap[B](f: A => Cont[R, B]): Cont[R, B] = Cont { (k: B => R) =>
      runCont((a: A) => f(a).runCont(k))
    }
  }

  implicit class RunCont[A](val cont: Cont[A, A]) extends AnyVal {
    @inline
    def run: A = cont.runCont(a => a)
  }

  object Cont {
    def pure[R, A](a: A): Cont[R, A] = cont(k => k(a))
  }

  @inline
  def cont[R, A](f: (A => R) => R): Cont[R, A] = Cont(f)

  // @inline
  def callCC[R, A, B](f: (A => Cont[R, B]) => Cont[R, A]): Cont[R, A] = cont { k =>
    f(a => cont(_ => k(a))).runCont(k)
  }

}

object ContMonad_Throw {
  import ContMonad._

  case class DivideByZero(a: Int)

  /*
    def div[R](a: Int, b: Int): Int = {
      if (a == 0) throw DivideByZero(a)
      a / b
    }
  */

  def tryCont[R, E, A](h: E => Cont[R, A])(c: (E => Cont[R, A]) => Cont[R, A]): Cont[R, A] =
    callCC[R, A, E] { ok =>
      val ifErr = callCC[R, E, A] { notOk =>
        c(notOk) flatMap ok
      }

      ifErr flatMap h
    }

  def div[R](a: Int, b: Int)(onError: DivideByZero => Cont[R, Int]): Cont[R, Int] =
    tryCont(onError) { throws =>
      if (b == 0) throws(DivideByZero(a))
      else Cont.pure[R, Int](a / b)
    }

  val zero = Cont.pure[Int, Int](0)

  def test(a: Int, b: Int): Cont[Int, Int] = {
    require(a != 0)
    div(a, b)(err => zero)
  } ensuring { res =>
    res.run == 0 || b != 0 && res.run == (a / b)
  }

  def testOk(a: Int, b: Int): Cont[Int, Int] = {
    require(b != 0)
    div(a, b)(err => zero)
  } ensuring { _.run == (a / b) }

  def testThrows(a: Int, b: Int): Cont[Int, Int] = {
    require(b == 0)
    div(a, b)(err => zero)
  } ensuring { _.run == 0 }

  def groundTestOk = {
    assert(div(10, 2)(err => zero).run == 5)
  }

  def groundTestThrows = {
    assert(div(10, 0)(err => zero).run == 0)
  }
}

