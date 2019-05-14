/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.proof

import stainless.lang._
import stainless.annotation._

import scala.language.implicitConversions

/** Internal helper classes and methods for the 'proof' package. */
object Internal {

  /*** Helper classes for relational reasoning ***/
  @library
  case class WithRel[A, B](x: A, r: (A, B) => Boolean, prop: Boolean) {

    /** Continue with the next relation. */
    def ^^(y: B): RelReasoning[B] = {
      require(prop ==> r(x, y))
      RelReasoning(y, prop && r(x, y))
    }

    /** Add a proof. */
    def ^^|(proof: Boolean): WithProof[A, B] = {
      require(proof)
      WithProof(x, r, proof, prop)
    }

    /** Short-hand for equational reasoning. */
    def ==|(proof: Boolean): WithProof[A, A] = {
      require(proof)
      WithProof(x, _ == _, proof, prop)
    }

    def qed: Boolean = prop
  }

  @library
  case class WithProof[A, B](
    x: A, r: (A, B) => Boolean, proof: Boolean, prop: Boolean) {

    /** Close a proof. */
    def |[C](that: WithProof[B, C]): WithProof[B, C] = {
      require(this.prop && this.proof ==> this.r(this.x, that.x))
      WithProof(
        that.x, that.r, that.proof,
        this.prop && this.proof && this.r(this.x, that.x))
    }

    /** Close a proof. */
    def |[C](that: WithRel[B, C]): WithRel[B, C] = {
      require(this.prop && this.proof ==> this.r(this.x, that.x))
      WithRel(
        that.x, that.r,
        this.prop && this.proof && this.r(this.x, that.x))
    }

    /** Close a proof. */
    def |(that: RelReasoning[B]): RelReasoning[B] = {
      require(this.prop && this.proof ==> this.r(this.x, that.x))
      RelReasoning(
        that.x,
        this.prop && this.proof && this.r(this.x, that.x))
    }
  }
}
