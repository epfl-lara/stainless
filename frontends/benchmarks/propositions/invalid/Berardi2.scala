/**
  * See discussion in https://github.com/epfl-lara/stainless/issues/173
  * Taken from https://gist.github.com/jad-hamza/62ac1947b28ff05113463b861073f4b8#file-berardi2-scala
  *
  *
  * References:
  * https://github.com/FStarLang/FStar/blob/master/examples/paradoxes/berardi_minimal.fst
  * https://coq.inria.fr/library/Coq.Logic.Berardi.html
  * https://github.com/FStarLang/FStar/issues/360
  * Proof-irrelevance out of Excluded-middle and Choice in the Calculus of Constructions.
  * F. Barbanera and S. Berardi. 1996.
  */

import stainless.lang._
import stainless.annotation._

object Berardi2 {
  def exists[T](p: T => Boolean) = {
    !forall((t: T) => !p(t))
  }

  def no[A] = forall((x: A) => false)
  def yes[A] = exists((x: A) => true)

  def cem[A]: Either[A, A => Unit] = {
    if (yes[A]) Left(choose((x: A) => true))
    else {
      assert(no[A])
      Right((x: A) => ())
    }
  }

  type Pow[A] = A => Boolean

  def jixx[A,B](i: A => B, j: B => A, x: A) = j(i(x)) == x

  def foralljixx[A,B](i: A => B, j: B => A) = forall((x: A) => jixx(i,j,x))

  case class Retract[A,B](i: A => B, j: B => A) {
    require(foralljixx(i,j))
  }

  case class RetractCond[A,B](i2: A => B, j2: B => A) {
    require(forall((r: Retract[A,B]) => foralljixx(i2,j2)))
  }

  def l1[A,B](): RetractCond[Pow[A],Pow[B]] = cem[Retract[Pow[A],Pow[B]]] match {
    case Left(Retract(i,j)) =>
      RetractCond(i,j)
    case Right(nr) =>
      def i(x: Pow[A]): Pow[B] = (y: B) => false
      def j(x: Pow[B]): Pow[A] = (y: A) => false
      RetractCond(i,j) // "Quantification does not fit in supported fragment"
  }

  trait U {
    def u[X](): Pow[X]
  }

  case class R() extends U {
    def u[X](): Pow[X] = {
      val lX: Pow[U] => Pow[X] = l1[X,U]().j2
      val rU: Pow[U] => Pow[U] = l1[U,U]().i2
      lX(rU(u => !u.u[U]()(u)))
    }
  }

  // The @ghost is to not have the snippet rejected due to testing for lambda equality
  @ghost
  def russel() = {
    val r = R()
    val l = l1[U,U]()
    val i2: Pow[U] => Pow[U] = l.i2
    val j2: Pow[U] => Pow[U] = l.j2
    assert(forall((r: Retract[U,U]) => foralljixx(i2,j2))) // "Quantification does not fit in supported fragment"
    assert(foralljixx(i2,j2)) // "Quantification does not fit in supported fragment"
    assert(forall((x: Pow[U]) => jixx(i2,j2,x)))
    assert(jixx(i2,j2,(u: U) => !u.u[U]()(u)))
    assert(j2(i2(u => !u.u[U]()(u))) == ((u: U) => !u.u[U]()(u)))
    assert(r.u[U]()(r) == j2(i2(u => !u.u[U]()(u)))(r))
    assert(r.u[U]()(r) == !r.u[U]()(r))
    assert(false)
  }
}