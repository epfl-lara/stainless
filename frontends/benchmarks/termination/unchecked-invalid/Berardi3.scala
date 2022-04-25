/**
  * See discussion in https://github.com/epfl-lara/stainless/issues/173
  * Taken from https://gist.github.com/jad-hamza/62ac1947b28ff05113463b861073f4b8#file-berardi3-scala
  *
  * References:
  * https://github.com/FStarLang/FStar/blob/master/examples/paradoxes/berardi_minimal.fst
  * https://coq.inria.fr/library/Coq.Logic.Berardi.html
  * https://github.com/FStarLang/FStar/issues/360
  * Proof-irrelevance out of Excluded-middle and Choice in the Calculus of Constructions.
  * F. Barbanera and S. Berardi. 1996.
  */

import stainless.lang._

object Berardi3 {
  def exists[T](p: T => Boolean) = {
    !forall((t: T) => !p(t))
  }

  def forallElim[T](p: T => Boolean, t: T) = {
    require(forall(p))
    p(t)
  }.holds

  // The dummy Int is there to ensure that the Scala compiler does not synthesize
  // a default-constructed False object (which would trigger the class invariant).
  case class False(dummy: Int) {
    require(false)
  }

  def mkFalse(f: False) = {
    // Trying to trick the solver to unfold the class invariant by gesticulating
    assert(f == f)
    val x = f.dummy
    assert(f.dummy == x)
    false
  }.holds

  type Not[A] = A => False

  def cem[A](): Either[A,Not[A]] = {
    if (exists((a: A) => true))
      Left(choose((a: A) => true))
    else {
      assert(forall((x: A) => false))
      Right((x: A) => False(123))
    }
  }

  type Pow[A] = A => Boolean

  def jixx[A,B](i: A => B, j: B => A, x: A) = j(i(x)) == x

  def foralljixx[A,B](i: A => B, j: B => A) = forall((x: A) => jixx(i,j,x))

  def foralljixx2[A,B](r: Retract[A,B], i: A => B, j: B => A) = forall((x: A) => jixx(i,j,x))

  case class Retract[A,B](i: A => B, j: B => A) {
    require(foralljixx(i,j))
  }

  case class RetractCond[A,B](i2: A => B, j2: B => A) {
    require(forall((r: Retract[A,B]) => foralljixx(i2,j2)))

    def instantiate(r: Retract[A,B]) = {
      assert(forall((r: Retract[A,B]) => foralljixx(i2,j2)))
      assert(forallElim((r: Retract[A,B]) => foralljixx(i2,j2), r))
      foralljixx(i2,j2)
    }.holds
  }

  def helper1[A,B](nr: Retract[A,B] => False, r: Retract[A,B], i: A => B, j: B => A) = {
    assert(mkFalse(nr(r)))
    foralljixx(i,j)
  }.holds

  def helper2[A,B](nr: Retract[A,B] => False, i: A => B, j: B => A) = {
    assert(forall((r: Retract[A,B]) => {
      helper1(nr,r,i,j) &&
      foralljixx(i,j)
    }))
    forall((r: Retract[A,B]) => {
      foralljixx(i,j)
    })
  }.holds

  def l1[A,B](): RetractCond[Pow[A],Pow[B]] = cem[Retract[Pow[A],Pow[B]]]() match {
    case Left(Retract(i,j)) =>
      RetractCond(i,j)
    case Right(nr) =>
      def i[A,B](x: Pow[A]): Pow[B] = (y: B) => false
      def j[A,B](x: Pow[B]): Pow[A] = (y: A) => false
      assert(helper2[Pow[A],Pow[B]](nr, i, j))
      RetractCond[Pow[A],Pow[B]](i,j)
  }

  trait U {
    def u[X](): Pow[X]
  }

  case class R() extends U {
    def u[X](): Pow[X] = {
      val lX: Pow[U] => Pow[X] = l1[X,U]().j2
      val rU: Pow[U] => Pow[U] = l1[U,U]().i2
      // "Measure decrease unknown" with --type-checker=true
      // but accepted otherwise :(
      lX(rU(u => !u.u[U]()(u)))
    }
  }

  val r = R()
  val l: RetractCond[Pow[U],Pow[U]] = l1[U,U]()
  val i2: Pow[U] => Pow[U] = l.i2
  val j2: Pow[U] => Pow[U] = l.j2

  def russel() = {
    // the following three assertions are used to prove that
    // { j2(i2(u => !u.u[U]()(u))) } = { u => !u.u[U]()(u) }
    assert(l.instantiate(Retract(x => x, x => x)))
    assert(foralljixx(i2,j2))
    assert(jixx(i2,j2,(u: U) => !u.u[U]()(u)))

    // there
    assert(r.u[U]()(r) == j2(i2(u => !u.u[U]()(u)))(r)) // by definition
    assert(r.u[U]()(r) == !r.u[U]()(r)) // because we prove that { j2(i2(u => !u.u[U]()(u))) } = { u => !u.u[U]()(u) }
    assert(false)
  }
}