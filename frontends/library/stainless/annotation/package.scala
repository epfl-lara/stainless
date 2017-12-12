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

  /** Only extract the contracts and replace the annotated function's body with a choose. */
  @ignore
  class extern     extends Annotation

}

