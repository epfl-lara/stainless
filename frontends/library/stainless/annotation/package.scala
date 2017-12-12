/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import scala.annotation.Annotation

package object annotation {

  /** The annotated symbols is not extracted at all. For internal usage only. */
  private[stainless] class ignore extends Annotation


  /** The annotated function or class' methods are not verified
   *  by default (use --functions=... to override this). */
  @ignore
  class library    extends Annotation

  /** Apply the "induct" tactic during verification of the annotated function. */
  @ignore
  class induct     extends Annotation

  /** Introduce an inductive hypothesis on `name` when verifying the annotated function. */
  // FIXME is this supported? (if not, remove TraceInductTacticTest.scala.BAK)
  // FIXME what does the default value "" mean/how is it handled?
  // FIXME using default value results in: [ Error  ] monotonicity$0 depends on missing dependencies: <init>$default$1$0.
  @ignore
  class traceInduct(name: String = "") extends Annotation

  /** Only extract the contracts and replace the annotated function's body with a choose. */
  @ignore
  class extern     extends Annotation

  /** Ensure that calling the annotated function had no side effect. */
  // FIXME There's no invalid test for this annotation.
  @ignore
  class pure       extends Annotation

}

