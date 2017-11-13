/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import scala.annotation.Annotation

package object annotation {

  class ignore     extends Annotation

  @ignore
  class library    extends Annotation
  @ignore
  class induct     extends Annotation
  @ignore
  class traceInduct(name: String = "") extends Annotation
  @ignore
  class extern     extends Annotation
  @ignore
  class internal   extends Annotation
  @ignore
  class pure       extends Annotation
  @ignore
  class force      extends Annotation

  // Orb annotations
  @ignore
  class monotonic  extends Annotation
  @ignore
  class compose    extends Annotation
  @ignore
  class axiom 		extends Annotation
  @ignore
  class invstate extends Annotation
  @ignore
  class memoize extends Annotation
  @ignore
  class invisibleBody extends Annotation // do not unfold the body of the function
  @ignore
  class usePost extends Annotation // assume the post-condition while proving time bounds
  @ignore
  class unfoldFactor(f: Int=0) extends Annotation // 0 implies no bound on unfolding
}
