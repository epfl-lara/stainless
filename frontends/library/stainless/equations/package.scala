/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

import stainless.lang._
import stainless.annotation._

import scala.language.implicitConversions

package object equations {

  @library
  case class ProofOps(prop: Boolean) {
    def because(proof: Boolean): Boolean = proof && prop
  }

  @library @inline
  implicit def boolean2ProofOps(prop: Boolean): ProofOps = ProofOps(prop)

  @library
  def trivial: Boolean = true

  @library @inline
  implicit def any2EqEvidence[A](x: => A): EqEvidence[A] = EqEvidence(() => x, () => x, () => true)

  @library
  case class EqEvidence[A](x: () => A, y: () => A, evidence: () => Boolean) {
    require(x() == y() && evidence())

    @inline
    def ==|(proof: => Boolean): EqEvidence[A] = {
      require(proof)
      EqEvidence(x, y, () => proof)
    }

    @inline
    def |:(prev: EqEvidence[A]): EqEvidence[A] = {
      require(prev.evidence() ==> (prev.y() == x()))
      EqEvidence(prev.x, y, prev.evidence)
    }

    @inline
    def qed: Boolean = (x() == y()).holds
  }
}
