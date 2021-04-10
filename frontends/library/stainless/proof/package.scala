/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import stainless.annotation._
import stainless.proof.Internal._
import stainless.lang._
import stainless.lang.StaticChecks._

import scala.language.implicitConversions


package object proof {

  @library
  case class ProofOps(prop: Boolean) {
    def because(proof: Boolean): Boolean = proof && prop

    // @ghost
    def neverHolds: Boolean = {
      require(!prop)
      !prop
    }
  }

  @library @inline
  implicit def boolean2ProofOps(prop: Boolean): ProofOps = ProofOps(prop)

  @library
  def trivial: Boolean = true

  @library
  def by(proof: Boolean)(prop: Boolean): Boolean =
    proof && prop

  @library @inline // @ghost
  def check(prop: Boolean): Unit = {
    require(prop)
    ()
  }.ensuring(_ => prop)

  /**
   * Relational reasoning.
   *
   *         {
   *           ((y :: ys) :+ x).last   ^^ _ == _ ^^| trivial         |
   *           (y :: (ys :+ x)).last   ==| trivial         |
   *           (ys :+ x).last          ==| snocLast(ys, x) |
   *           x
   *         }.qed
   */
  @library
  case class RelReasoning[A](x: A, prop: Boolean) {

    def ^^[B](r: (A, B) => Boolean): WithRel[A, B] = WithRel(x, r, prop)

    /** Short-hand for equational reasoning. */
    def ==|(proof: Boolean): WithProof[A, A] = {
      require(proof)
      WithProof(x, _ == _, proof, prop)
    }

    def qed: Boolean = prop
  }

  @library
  implicit def any2RelReasoning[A](x: A): RelReasoning[A] =
    RelReasoning(x, true)

}

