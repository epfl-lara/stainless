/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package xlang

trait ExprOps extends innerclasses.ExprOps { self =>
  protected val trees: Trees
  import trees._
}
